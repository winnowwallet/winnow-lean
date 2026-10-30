import WinnowApp.Real.Wallet

/-! # Fees, sending, fee bumps, payment details, and the mempool windows

AppModel.swift: `resolvedFeeRate` (:1539), `SendPreview.authorizes` (:1654), `previewSend` (:1695,
:1722), `exclusively` / `operationsInFlight` (:1783–1800), `send(preview:)` (:1802), `pendingFeeRate` /
`previewFeeBump` / `bumpFee` (:1837–1880), `broadcast` (:1886), `rawTransactionHex` (:899),
`loadPaymentDetails` (:2191). The windows: `makeMempoolWindow` (:238) as ReceiveView's `openWindow` /
`closeWindow` and SendView's `watchBroadcastEvents` use it.

A reviewed send or fee bump is kept here with everything `authorizes` needs; the app's `Preview` and
`FeeBumpPreview` are its summary, and `sendPayment` / `bumpFee` accept only a summary that matches a
kept review exactly (anything else is `sendReviewChanged`). -/

namespace WinnowApp.Real
open Winnow Winnow.IO Winnow.Net

def priorityOf : Nat → FeePolicy.Priority
  | 0 => .low
  | 2 => .high
  | _ => .medium

/-- `resolvedFee(priority:override:)`: override, the wallet's observed median, the preset; raised to the
peers' seat-majority BIP133 floor up to the 120 sat/vB cap, which `clampedFloor` reports. -/
def resolveFee (env : Env) (priority : Nat) (overrideMilli : Option Nat) : IO FeePolicy.Resolution := do
  let c ← env.get
  let observed ← match c.wallet with
    | some w => w.observedFeeRates
    | none => pure #[]
  let floor ← match c.stack with
    | some s => feeFloor s.pool .seatMajority
    | none => pure none
  return FeePolicy.resolution (priorityOf priority) (overrideMilli.map rateOfMilli) none observed floor

/-- `resolvedFeeRate(priority:override:)`. -/
def resolveRate (env : Env) (priority : Nat) (overrideMilli : Option Nat) : IO Float := do
  return (← resolveFee env priority overrideMilli).rate

/-- `requireRelayFee(rate:floor:)`. -/
def requireRelayFee (rate : Float) (floor : Option Float) : IO Unit := do
  if let some f := floor then
    if rate < f then failWith (.feeDecisionRequired rate f)

/-- `requireRelayFloors(rate:)`: the live floors a rate must clear before anything is signed or announced:
the seat majority, which prices the quote, and the most lenient connected peer, below which nobody
connected would relay (so empty seats cannot outvote a lone peer's floor). No stack, no floor. -/
def requireRelayFloors (env : Env) (rate : Float) : IO Unit := do
  let some s := (← env.get).stack | return
  requireRelayFee rate (← feeFloor s.pool .seatMajority)
  requireRelayFee rate (← feeFloor s.pool .mostLenient)

/-- `authorizes(transaction:fee:changeAmount:resolvedSilentPayments:)`: the same check on a transaction
that is not yet signed, such as a multisig account's PSBT, whose inputs, outputs and fee are fixed
before any signature. -/
def SendReview.authorizesTransaction (r : SendReview) (tx : Transaction) (fee : Int64) (changeAmount : Option Int64)
    (resolved : Array Payment := #[]) : Bool := Id.run do
  if !(fee == r.fee && changeAmount == r.changeAmount &&
      tx.inputs.map (·.previousOutput) == r.selected) then return false
  if !(resolved.size == r.silentPayments.size &&
      (r.silentPayments.zip resolved).all fun (s, p) => s.amount == p.amount) then return false
  let reviewed := r.payments ++ resolved
  let expected := match r.change with | some c => reviewed.push c | none => reviewed
  if tx.outputs.size != expected.size then return false
  let mut unmatched := tx.outputs
  for p in expected do
    match unmatched.findIdx? (fun o => o.value == p.amount && o.scriptPubKey == p.scriptPubKey) with
    | some i => unmatched := unmatched.eraseIdx! i
    | none => return false
  if !unmatched.isEmpty then return false
  return r.change.isNone == r.changeAmount.isNone

/-- `SendPreview.authorizes(_:resolvedSilentPayments:)`: fee, change, inputs in order, and the outputs
exactly. A silent payment's script comes from the wallet (`resolved`, one per reviewed silent payment, same
order and amount) and is then matched like any reviewed payment. -/
def SendReview.authorizes (r : SendReview) (built : BuiltTransaction) (resolved : Array Payment := #[]) : Bool :=
  r.authorizesTransaction built.transaction built.fee built.changeAmount resolved

def sameSummary (a b : Preview) : Bool :=
  a.destination == b.destination && a.amount == b.amount && a.fee == b.fee &&
    a.feeRateMilli == b.feeRateMilli && a.inputCount == b.inputCount && a.change == b.change &&
    a.recipient == b.recipient && a.account == b.account

/-- `previewSend(destination:…)` / `previewSend(to:…)` for the everyday wallet. -/
def previewSend (env : Env) (inputs : SendInputs) : IO Preview := do
  -- `requireUsableOverride`: an override outside the band is refused where it was typed
  if let some o := parseRateMilli inputs.override then
    unless FeePolicy.acceptsRate (rateOfMilli o) do failText (CoinSelectionError.invalidFeeRate (rateOfMilli o)).description
  let resolution ← resolveFee env inputs.priority (parseRateMilli inputs.override)
  requireRelayFee resolution.rate resolution.clampedFloor
  requireRelayFloors env resolution.rate
  let feeRate := resolution.rate
  let (destination, recipient) ← match inputs.personID with
    | some id => do
      let (address, index, r) ← env.hooks.personPayment id
      pure (address, some (id, index, r))
    | none => pure (inputs.destination.trimAscii.copy, none)
  let amount := inputs.amount.trimAscii.copy.toNat?.getD 0
  let c ← env.get
  let some n := c.network | failWith .noWallet
  -- `parseDestination`: a silent payment code (its HRP checked against this network), else an address
  let (payments, silent) ← if SilentPaymentAddress.looksLikeCode destination then
      match Keys.SilentPayment.ofCode (i64 amount) destination (Network.tx n) with
      | .ok p => pure (#[], #[p])
      | .error e => failText (silentPaymentErrorText e)
    else match Payment.ofAddress (i64 amount) destination (Network.tx n) with
      | .ok p => pure (#[p], #[])
      | .error e => failText (addressErrorText e)
  let some w := c.wallet | failWith .noWallet
  let utxos ← w.spendableUtxos
  let changeScript ← runWM (w.scriptPubKey .change (← w.nextChangeIndex))
  let sizing := payments ++ silent.map fun p => { amount := p.amount, scriptPubKey := Keys.SilentPayment.sizingScriptPubKey }
  let selection ← match CoinSelection.select utxos sizing changeScript feeRate with
    | .ok s => pure s
    | .error e => failText e.description
  let phase ← updateSyncPhase env
  let summary : Preview :=
    { destination, amount, fee := natOf selection.fee, feeRateMilli := milliOf feeRate,
      inputCount := selection.selected.size, change := selection.changeAmount.map natOf,
      locktimeLagsTip := phase.headerTipMayLagNetwork,
      recipient := recipient.map fun (_, _, r) => r, silent := !silent.isEmpty }
  let review : SendReview :=
    { inputs, summary, payments, silentPayments := silent, feeRate, fee := selection.fee, changeAmount := selection.changeAmount,
      selected := selection.selected.map (·.outpoint),
      change := selection.changeAmount.map fun a => { amount := a, scriptPubKey := changeScript }
      recipient := recipient.map fun (id, index, r) => (id, if r.derivesFreshAddresses then some index else none) }
  env.modify fun c => { c with reviews := ((c.reviews.filter (·.inputs != inputs)).push review).extract 0 16 }
  return summary

/-- `exclusively(.spending)`: the check and the claim with no interleaving between them. -/
def exclusively {α} (env : Env) (act : IO α) : IO α := do
  let claimed ← env.modifyGet fun c => if c.spending then (false, c) else (true, { c with spending := true })
  if !claimed then failWith .spendAlreadyInFlight
  try act finally env.modify fun c => { c with spending := false }

/-- `broadcast(_:feeRateSatPerVByte:)`: P2P relay only. -/
def broadcastTx (env : Env) (tx : Transaction) (rate : Option Float) : IO ByteArray := do
  let some s := (← env.get).stack | failWith .noStack
  -- the final gate: the live floors again, as the review saw them may have moved
  if let some r := rate then requireRelayFloors env r
  let raw := tx.serialized true
  let txid ← runNet (s.broadcaster.broadcast raw rate)
  env.journal "transaction.broadcast" [("txid", Winnow.displayHex txid), ("raw", hex raw)]
  return txid

/-- `send(preview:)` after authentication: rebuild, sign, check `authorizes`, broadcast, commit. -/
def sendPayment (env : Env) (inputs : SendInputs) (p : Preview) : IO SentPayment := exclusively env do
  let c ← env.get
  let some w := c.wallet | failWith .noWallet
  let some review := c.reviews.find? (fun r => r.inputs == inputs && sameSummary r.summary p) | failWith .sendReviewChanged
  let tip ← match c.stack with
    | some s => s.chain.height
    | none => pure 0
  let prepared ← env.walletOp (w.buildSend review.payments review.feeRate tip (silentPayments := review.silentPayments))
  unless review.authorizes prepared.built prepared.resolvedSilentPayments do failWith .sendReviewChanged
  let txid ← broadcastTx env prepared.built.transaction (some review.feeRate)
  env.walletOp (w.commit prepared)
  if let some (id, some index) := review.recipient then env.hooks.advancePersonIndex id index
  if let some r := review.summary.recipient then
    env.journal "person.paid" [("name", r.name),
      ("paymentIndex", ((review.recipient.bind (·.2)).map toString).getD "fixed"), ("txid", Winnow.displayHex txid)]
  env.modify fun c => { c with reviews := c.reviews.filter (·.inputs != inputs) }
  env.journal "transaction.sent" [("txid", Winnow.displayHex txid), ("raw", hex (prepared.built.transaction.serialized true)),
    ("silent", toString !review.silentPayments.isEmpty),
    ("silentOutputs", ",".intercalate (prepared.resolvedSilentPayments.toList.map (hex ·.scriptPubKey)))]
  let net := ((← env.get).network.map Network.tx).getD .signet
  return { txid := Winnow.displayHex txid,
           derivedAddresses := prepared.resolvedSilentPayments.toList.filterMap (AddressDecoder.address ·.scriptPubKey net) }

/-- `rawTransactionHex(_:)`: the signed bytes of a still-pending transaction. -/
def rawTransactionHex (env : Env) (txid : String) : IO (Option String) := do
  let some s := (← env.get).stack | return none
  return (← s.broadcaster.rawTransaction (ofDisplayHex! txid)).map hex

/-- `pendingFeeRate(txid:)`: thousandths of sat/vB, and HomeView's suggestion from the unrounded rate. -/
def pendingFeeRate (env : Env) (txid : String) : IO (Nat × String) := do
  let some w := (← env.get).wallet | failWith .noWallet
  let rate ← runWM (w.pendingFeeRate (ofDisplayHex! txid))
  return (milliOf rate, suggestedBumpText rate)

def bumpSummary (p : Winnow.FeeBumpPreview) : WinnowApp.FeeBumpPreview :=
  { feeRateMilli := milliOf p.feeRateSatPerVByte, fee := natOf p.fee, change := p.changeAmount.map natOf }

/-- `previewFeeBump(txid:feeRateSatPerVByte:)`; the full preview is kept for `bumpFee`. -/
def previewFeeBump (env : Env) (txid : String) (milli : Nat) : IO WinnowApp.FeeBumpPreview := do
  let some w := (← env.get).wallet | failWith .noWallet
  -- refused at review, before authentication and signing; `broadcastTx` asks again
  requireRelayFloors env (rateOfMilli milli)
  let p ← runWM (w.previewFeeBump (ofDisplayHex! txid) (rateOfMilli milli))
  env.modify fun c => { c with bumps := ((c.bumps.filter (·.1 != txid)).push (txid, p)).extract 0 16 }
  return bumpSummary p

/-- `bumpFee(preview:)` after authentication: broadcast the replacement, commit the swap (cancelling
the replacement's relay if that fails), then stop relaying the original. -/
def bumpFee (env : Env) (txid : String) (p : WinnowApp.FeeBumpPreview) : IO String := exclusively env do
  let c ← env.get
  let some w := c.wallet | failWith .noWallet
  let some s := c.stack | failWith .noStack
  let some (_, preview) := c.bumps.find? (fun (t, b) => t == txid && bumpSummary b == p) | failWith .sendReviewChanged
  let prepared ← env.walletOp (w.buildFeeBump preview.originalTxid preview.feeRateSatPerVByte)
  unless preview.authorizes prepared.built do failWith .sendReviewChanged
  let vsize := TransactionBuilder.vsize prepared.built.transaction
  let rate := Float.ofInt prepared.built.fee.toInt / vsize.toFloat
  let replacement ← broadcastTx env prepared.built.transaction (some rate)
  try env.walletOp (w.commitFeeBump prepared)
  catch e =>
    runNet (s.broadcaster.cancel replacement)
    throw e
  runNet (s.broadcaster.cancel preview.originalTxid)
  env.modify fun c => { c with bumps := c.bumps.filter (·.1 != txid) }
  env.journal "transaction.replaced" [("original", Winnow.displayHex preview.originalTxid),
    ("replacement", Winnow.displayHex replacement), ("raw", hex (prepared.built.transaction.serialized true))]
  return Winnow.displayHex replacement

/-- `loadPaymentDetails(_:)`: the stored raw transaction from the relay queue or its block. -/
def loadPaymentDetails (env : Env) (txid : String) : IO Unit := do
  let c ← env.get
  let some w := c.wallet | return
  let some s := c.stack | return
  let id := ofDisplayHex! txid
  let some entry := (← w.history).find? (·.txid == id) | return
  if entry.rawTransaction.isSome then return
  let tx ← match ← s.broadcaster.rawTransaction id with
    | some raw => match Transaction.decode raw with
      | .ok t => pure t
      | .error e => failText (NetError.wire e).description
    | none =>
      match s.filters with
      | some f => if entry.height > 0 then runNet (f.transaction id entry.height) else failWith .paymentDetailsUnavailable
      | none => failWith .paymentDetailsUnavailable
  let c' ← env.get
  if c'.generation != c.generation || !(c'.wallet.map (·.id) == some w.id) then return
  env.walletOp (w.rememberTransaction tx)

/-! ## Mempool windows -/

/-- Registers a window for this generation, or closes it when the generation is already over. -/
def registerRelayWindow (env : Env) (gen : Nat) (w : Window) : IO (Option Nat) := do
  let id ← env.modifyGet fun c =>
    if c.generation != gen then (none, c)
    else (some c.nextWatchId, { c with nextWatchId := c.nextWatchId + 1, relayWindows := c.relayWindows.push (c.nextWatchId, w) })
  if id.isNone then w.close
  return id

/-- ReceiveView's window on the displayed address: `seen txid amount` per relayed payment. -/
def watchAddress (env : Env) (address : String) (seen : String → Int → IO Unit) : IO Unit := do
  let c ← env.get
  let some s := c.stack | return
  let some n := c.network | return
  let .ok script := AddressDecoder.scriptPubKey address (Network.tx n) | return
  let window ← MempoolWindowIO.new s.pool #[script]
  let events ← window.events
  let w : Window := { window, events }
  let (old, installed) ← env.modifyGet fun c' =>
    if c'.generation != c.generation then ((none, false), c')
    else ((c'.receiveWindow, true), { c' with receiveWindow := some w })
  if let some o := old then o.close
  unless installed do
    w.close
    return
  window.start
  env.spawnLoop do
    repeat
      match ← events.next with
      | .value (.paymentSeen txid amount _) => seen (Winnow.displayHex txid) amount.toInt
      | .value _ => pure ()
      | .finished _ => break

def stopWatchingAddress (env : Env) : IO Unit := do
  let old ← env.modifyGet fun c => (c.receiveWindow, { c with receiveWindow := none })
  if let some o := old then o.close

/-- SendView's `watchBroadcastEvents`: broadcaster events plus mempool-window echoes, until confirmed. -/
def watchRelay (env : Env) (txid : String) (report : RelayEvent → IO Unit) : IO Unit := do
  let c ← env.get
  let some s := c.stack | return
  let id := ofDisplayHex! txid
  let window ← MempoolWindowIO.new s.pool #[]
  window.watchEcho id
  let echoes ← window.events
  let w : Window := { window, events := echoes }
  let some watchId ← registerRelayWindow env c.generation w | return
  let relay ← s.broadcaster.events
  window.start
  env.spawnLoop do
    repeat
      match ← echoes.next with
      | .value (.txidEchoed t peer) => if t == id then report (.echoed peer.description)
      | .value _ => pure ()
      | .finished _ => break
  env.spawnLoop do
    try
      repeat
        match ← relay.next with
        | .value (.announced t k) => if t == id then report (.announced k)
        | .value (.requested t peer) => if t == id then report (.requested peer.description)
        | .value (.feeFloorExceeded t _) => if t == id then report .feeFloorExceeded
        | .value (.confirmed t) =>
          if t == id then
            report .confirmed
            break
        | .value _ => pure ()
        | .finished _ => break
    finally
      relay.cancel
      w.close
      env.modify fun c => { c with relayWindows := c.relayWindows.filter (·.1 != watchId) }

end WinnowApp.Real
