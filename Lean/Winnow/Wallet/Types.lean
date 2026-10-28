import Winnow.Wallet.SwiftJSON
import Winnow.Tx.Transaction
import Winnow.Tx.TransactionBuilder
import Winnow.Tx.SighashBIP341
import Winnow.Tx.PSBT
import Winnow.Keys.SilentPayments

/-! # Wallet data types and the wallet file

Port of the data half of `Sources/WalletCore/Wallet/Wallet.swift`: `WalletError`, `FeeBumpError`,
`AddressChain`, `WalletUTXO` (+ `SpentMarker`), `HistoryEntry`, `MatchEffect`, `PendingSend`,
`WalletState` with their hand-written `Codable` forms, `BuiltTransaction` and `FeeBumpPreview`, and
`HistoryEntry.Outputs` (`Wallet/HistoryOutputs.swift`, upstream 1cf93fb: the recipient and change outputs
of a locally prepared send). The `Wallet` actor itself is not here.

JSON (see `SwiftJSON`): txids are display-order hex, scripts hex, `Data` fields that use the synthesized
coding (`SpentMarker.spentBy`, `rawTransaction`, `fundingScripts`) base64. Decoders run in the Swift
order, so the first failing field names the same error. -/

namespace Winnow
open SwiftJSON

/-! ## Errors -/

inductive WalletError where
  | invalidDescriptor (s : String)
  | descriptorMismatch
  /-- The loaded signing key does not belong to the descriptor's account. -/
  | accountKeyMismatch
  | invalidBundle (reason : String)
  | noPayments
  | changeOutputMissing
  | transactionTooLarge (vsize limit : Int)
  | mnemonicUnavailable
  | exportWhilePending
  | invalidTransactionAmounts
  | unsupportedWalletData
  | storageTooLarge (maxBytes : Int)
  deriving Inhabited, BEq

namespace WalletError
def name : WalletError → String
  | .invalidDescriptor _ => "invalidDescriptor" | .descriptorMismatch => "descriptorMismatch"
  | .accountKeyMismatch => "accountKeyMismatch"
  | .invalidBundle _ => "invalidBundle" | .noPayments => "noPayments"
  | .changeOutputMissing => "changeOutputMissing" | .transactionTooLarge .. => "transactionTooLarge"
  | .mnemonicUnavailable => "mnemonicUnavailable" | .exportWhilePending => "exportWhilePending"
  | .invalidTransactionAmounts => "invalidTransactionAmounts" | .unsupportedWalletData => "unsupportedWalletData"
  | .storageTooLarge _ => "storageTooLarge"

/-- `errorDescription`. -/
def description : WalletError → String
  | .invalidDescriptor _ =>
    "That wallet descriptor could not be parsed. It is not repeated here, " ++
      "because a descriptor can carry key material."
  | .descriptorMismatch => "Bundle descriptor does not match the mnemonic."
  | .accountKeyMismatch => "The signing key does not match this wallet's account."
  | .invalidBundle reason => s!"Invalid import bundle: {reason}"
  | .noPayments => "Nothing to send."
  | .changeOutputMissing => "The built transaction lost its change output."
  | .transactionTooLarge vsize limit => s!"The signed transaction is {vsize} vbytes, above the {limit}-vbyte relay maximum."
  | .mnemonicUnavailable =>
    "This wallet has no recovery phrase to export — it was imported from an extended key, not a BIP39 mnemonic."
  | .exportWhilePending =>
    "Wait for pending transactions to confirm before exporting. A mid-send backup would drop the coins being spent."
  | .invalidTransactionAmounts => "A matched Bitcoin transaction contains invalid amounts. Wallet state was not changed."
  | .unsupportedWalletData =>
    "This wallet contains unsupported signing data and cannot be opened here. " ++
      "Keep the original wallet file and use compatible wallet software to recover these coins."
  | .storageTooLarge maxBytes => s!"The wallet file is larger than the {maxBytes.tdiv 1_048_576} MB this wallet can hold and was not read."
end WalletError

inductive FeeBumpError where
  | transactionNotPending
  | noChangeOutput
  | changeAlreadySpent
  | invalidFeeRate (rate : Float)
  | feeRateNotHigher (current requested : Float)
  | insufficientChange (requiredFee maximumFee : Int64)
  deriving Inhabited

namespace FeeBumpError
def name : FeeBumpError → String
  | .transactionNotPending => "transactionNotPending" | .noChangeOutput => "noChangeOutput"
  | .changeAlreadySpent => "changeAlreadySpent" | .invalidFeeRate _ => "invalidFeeRate"
  | .feeRateNotHigher .. => "feeRateNotHigher" | .insufficientChange .. => "insufficientChange"

/-- `errorDescription` (the two-decimal rates are en_US `formatted`). -/
def description : FeeBumpError → String
  | .transactionNotPending =>
    "This transaction is no longer pending or was created before fee-bump metadata was available."
  | .noChangeOutput => "This transaction has no change output to reduce for a same-input fee bump."
  | .changeAlreadySpent => "This transaction's change has already been spent by another pending transaction."
  | .invalidFeeRate rate => s!"Invalid replacement fee rate: {SwiftDouble.description rate} sat/vB."
  | .feeRateNotHigher current requested =>
    s!"Choose a fee rate above {SwiftDouble.formatted2 current} sat/vB (requested {SwiftDouble.formatted2 requested} sat/vB)."
  | .insufficientChange requiredFee maximumFee =>
    s!"The available change can pay at most {maximumFee.toInt} sats in fees; this bump needs {requiredFee.toInt} sats."
end FeeBumpError

/-! ## Coins and history -/

/-- Which chain of the multipath descriptor an address is on (raw values 0 / 1). -/
inductive AddressChain where
  | receive | change
  deriving Inhabited, BEq, Repr

def AddressChain.rawValue : AddressChain → Nat | .receive => 0 | .change => 1

structure SpentMarker where
  spentBy : ByteArray
  height : Option UInt32
  deriving Inhabited, BEq

structure WalletUTXO where
  txid : ByteArray -- internal byte order
  vout : UInt32
  amount : Int64
  scriptPubKey : ByteArray
  chain : AddressChain
  index : UInt32
  height : UInt32
  isCoinbase : Bool := false
  spent : Option SpentMarker := none
  deriving Inhabited, BEq

namespace WalletUTXO
def isSpent (u : WalletUTXO) : Bool := u.spent.isSome
def outpoint (u : WalletUTXO) : Transaction.Outpoint := ⟨u.txid, u.vout⟩
def spentOutput (u : WalletUTXO) : SighashBIP341.SpentOutput := { amount := u.amount, scriptPubKey := u.scriptPubKey }
end WalletUTXO

/-- A recipient of a locally prepared send. -/
structure HistoryEntry.ExternalOutput where
  vout : UInt32
  amount : Int64
  /-- JSON uses hexadecimal, matching wallet coin scripts. -/
  scriptPubKey : ByteArray
  /-- The BIP352 silent payment code this output was derived for, when the send paid one. -/
  silentPaymentAddress : Option String := none
  deriving Inhabited, BEq

/-- A known output breakdown: wallet-owned receive outputs are omitted; `change` holds vouts and
`external` the recipients in transaction order. -/
structure HistoryEntry.Outputs where
  external : Array HistoryEntry.ExternalOutput := #[]
  change : Array UInt32 := #[]
  deriving Inhabited, BEq

structure HistoryEntry where
  txid : ByteArray
  height : UInt32
  received : Int64
  spent : Int64
  fee : Option Int64 := none
  replacedBy : Option ByteArray := none
  rawTransaction : Option ByteArray := none
  fundingScripts : Array ByteArray := #[]
  /-- The block this payment confirmed in (internal byte order); recorded, not yet verified. -/
  blockHash : Option ByteArray := none
  /-- Known recipient and change outputs from a locally prepared send; `none` means unavailable. -/
  outputs : Option HistoryEntry.Outputs := none
  deriving Inhabited, BEq

/-- What applying one matched block changed. -/
structure MatchEffect.Spend where
  txid : ByteArray
  vout : UInt32
  spentBy : ByteArray
  height : UInt32
  deriving Inhabited, BEq

structure MatchEffect where
  received : Array WalletUTXO := #[]
  spent : Array MatchEffect.Spend := #[]
  discardedReplacements : Array ByteArray := #[]
  deriving Inhabited, BEq

/-- Exact data of a locally-created, still-replaceable send. -/
structure PendingSend where
  rawTransaction : ByteArray
  selected : Array WalletUTXO
  changeIndex : Option UInt32
  changeOutputIndex : Option UInt32
  fee : Int64
  deriving Inhabited, BEq

structure WalletState where
  descriptor : String
  network : String
  creationHeight : UInt32
  nextReceiveIndex : UInt32 := 0
  nextChangeIndex : UInt32 := 0
  nextScanHeight : UInt32
  /-- The hash of block `nextScanHeight - 1` (internal byte order); recorded, not yet checked. -/
  scannedThroughHash : Option ByteArray := none
  allUtxos : Array WalletUTXO := #[]
  history : Array HistoryEntry := #[]
  observedFeeRates : Array Float := #[]
  pendingSends : Array PendingSend := #[]
  deriving Inhabited, BEq

def WalletState.utxos (s : WalletState) : Array WalletUTXO := s.allUtxos.filter (!·.isSpent)

/-- `Wallet.send`'s result. -/
structure BuiltTransaction where
  psbt : PSBT
  transaction : Transaction
  fee : Int64
  changeAmount : Option Int64
  deriving Inhabited

structure FeeBumpPreview where
  originalTxid : ByteArray
  currentFeeRateSatPerVByte : Float
  feeRateSatPerVByte : Float
  fee : Int64
  changeAmount : Option Int64
  replacementTransaction : Transaction
  deriving Inhabited

/-- Binds the signed replacement to the reviewed transaction (witnesses excluded). -/
def FeeBumpPreview.authorizes (p : FeeBumpPreview) (built : BuiltTransaction) : Bool :=
  let actual := built.transaction
  let reviewed := p.replacementTransaction
  let sameInputs := actual.inputs.size == reviewed.inputs.size &&
    (actual.inputs.zip reviewed.inputs).all fun (a, b) =>
      a.previousOutput == b.previousOutput && a.scriptSig == b.scriptSig && a.sequence == b.sequence
  if !(built.fee == p.fee && built.changeAmount == p.changeAmount && actual.version == reviewed.version &&
      actual.locktime == reviewed.locktime && actual.outputs == reviewed.outputs && sameInputs) then false
  else
    let vsize := TransactionBuilder.vsize actual
    vsize > 0 && Float.ofInt built.fee.toInt / vsize.toFloat == p.feeRateSatPerVByte

/-! ## Wallet constants other modules share (`Wallet.coinbaseMaturity`, `Wallet.checkStandardSize`) -/

namespace Wallet

/-- The receive/change lookahead past the last used index. -/
def gapLimit : UInt32 := 20

/-- Blocks a coinbase output must wait before it can be spent. -/
def coinbaseMaturity : UInt32 := 100

/-- Refuses a transaction past Bitcoin Core's standard size limit, measured on the signed bytes. -/
def checkStandardSize (tx : Transaction) : Except WalletError Unit := do
  let vsize := TransactionBuilder.vsize tx
  if vsize > TransactionBuilder.maximumStandardVSize then
    throw (.transactionTooLarge vsize TransactionBuilder.maximumStandardVSize)

end Wallet

/-! ## JSON -/

def displayHex (b : ByteArray) : String := hex (ByteArray.reverse b)

def hexField (kvs : Array (String × JV)) (k : String) : D ByteArray := do
  let s ← key kvs k asString
  match Wire.dataOfHex? s with
  | some b => pure b
  | none => dataCorrupted

def obj (kvs : List (String × Option JV)) : JV := .obj (kvs.filterMap fun (k, v) => v.map (k, ·)).toArray

namespace SpentMarker
def toJV (m : SpentMarker) : JV :=
  obj [("spentBy", some (ofData m.spentBy)), ("height", m.height.map (ofInt ·.toNat))]
def ofJV (v : JV) : D SpentMarker := do
  let kvs ← asObject v
  let spentBy ← key kvs "spentBy" asData
  let height ← keyIfPresent kvs "height" asUInt32
  return { spentBy, height }
end SpentMarker

namespace WalletUTXO
def toJV (u : WalletUTXO) : JV :=
  obj [("txid", some (.str (displayHex u.txid))), ("vout", some (ofInt u.vout.toNat)),
    ("amount", some (ofInt u.amount.toInt)), ("scriptPubKey", some (.str (hex u.scriptPubKey))),
    ("chain", some (ofInt u.chain.rawValue)), ("index", some (ofInt u.index.toNat)),
    ("height", some (ofInt u.height.toNat)), ("spent", u.spent.map SpentMarker.toJV),
    ("isCoinbase", if u.isCoinbase then some (.bool true) else none)]

def chainOfJV (v : JV) : D AddressChain := do
  match ← asInt v with
  | 0 => pure .receive
  | 1 => pure .change
  | _ => dataCorrupted

def ofJV (v : JV) : D WalletUTXO := do
  let kvs ← asObject v
  let txid ← hexField kvs "txid"
  let scriptPubKey ← hexField kvs "scriptPubKey"
  if contains kvs "silentPaymentTweak" then throw "unsupportedWalletData"
  let vout ← key kvs "vout" asUInt32
  let amount ← key kvs "amount" asInt64
  let chain ← key kvs "chain" chainOfJV
  let index ← key kvs "index" asUInt32
  let height ← key kvs "height" asUInt32
  let isCoinbase := (← keyIfPresent kvs "isCoinbase" asBool).getD false
  let spent ← keyIfPresent kvs "spent" SpentMarker.ofJV
  return { txid := ByteArray.reverse txid, vout, amount, scriptPubKey, chain, index, height, isCoinbase, spent }
end WalletUTXO

namespace HistoryEntry

/-! ### Outputs (`HistoryOutputs.swift`) -/

def strictlyIncreasing (xs : Array UInt32) : Bool := Id.run do
  for h : i in [1:xs.size] do
    if !(xs[i - 1]! < xs[i]!) then return false
  return true

/-- The breakdown's own consistency: increasing, disjoint indices; positive amounts within the supply;
non-empty scripts; any silent payment code one that parses. -/
def Outputs.validate (o : Outputs) : Except WalletError Unit := do
  let vouts := o.external.map (·.vout)
  unless strictlyIncreasing vouts && strictlyIncreasing o.change && !vouts.any o.change.contains do
    throw (.invalidBundle "history output indices contradict each other")
  let mut total : Int64 := 0
  for output in o.external do
    unless output.amount > 0 && output.amount ≤ bitcoinAmountMaximum - total && !output.scriptPubKey.isEmpty do
      throw (.invalidBundle "history output has an invalid amount or script")
    total := total + output.amount
    if let some code := output.silentPaymentAddress then
      unless (SilentPaymentAddress.parse code).toOption.isSome do
        throw (.invalidBundle "history output names an invalid silent payment code")

/-- A breakdown with transaction bytes must describe those exact outputs. -/
def Outputs.validateAgainst (o : Outputs) (tx : Transaction) : Except WalletError Unit := do
  for output in o.external do
    let ok := match tx.outputs[output.vout.toNat]? with
      | some t => t.value == output.amount && t.scriptPubKey == output.scriptPubKey
      | none => false
    unless ok do throw (.invalidBundle "history outputs do not match the transaction")
  unless o.change.all (·.toNat < tx.outputs.size) do
    throw (.invalidBundle "history change index is outside the transaction")

/-- Names the code each silent payment was derived for on the first unclaimed recipient output with its
amount and script (`annotateSilentPayments`). -/
def Outputs.annotateSilentPayments (o : Outputs) (resolved : Array (Int64 × ByteArray)) (codes : Array String) : Outputs := Id.run do
  let mut external := o.external
  let mut claimed : Array Nat := #[]
  for ((amount, script), code) in resolved.zip codes do
    match (List.range external.size).find? fun i =>
        !claimed.contains i && external[i]!.amount == amount && external[i]!.scriptPubKey == script with
    | some i =>
      external := external.modify i fun e => { e with silentPaymentAddress := some code }
      claimed := claimed.push i
    | none => pure ()
  return { o with external }

/-- Copies silent payment codes from a replaced transaction's outputs onto the outputs of its replacement
that carry the same script. -/
def Outputs.inheritSilentPayments (o : Outputs) (previous : Outputs) : Outputs :=
  let codes := previous.external.filterMap fun e => e.silentPaymentAddress.map (e.scriptPubKey, ·)
  -- A dictionary by script: the last code per script wins.
  { o with external := o.external.map fun e =>
      { e with silentPaymentAddress := ((codes.reverse.find? (·.1 == e.scriptPubKey)).map (·.2)) } }

def ExternalOutput.toJV (e : ExternalOutput) : JV :=
  obj [("vout", some (ofInt e.vout.toNat)), ("amount", some (ofInt e.amount.toInt)),
    ("scriptPubKey", some (.str (hex e.scriptPubKey))), ("silentPaymentAddress", e.silentPaymentAddress.map .str)]

def ExternalOutput.ofJV (v : JV) : D ExternalOutput := do
  let kvs ← asObject v
  let scriptPubKey ← hexField kvs "scriptPubKey"
  let vout ← key kvs "vout" asUInt32
  let amount ← key kvs "amount" asInt64
  let silentPaymentAddress ← keyIfPresent kvs "silentPaymentAddress" asString
  return { vout, amount, scriptPubKey, silentPaymentAddress }

def Outputs.toJV (o : Outputs) : JV :=
  obj [("external", some (.arr (o.external.map ExternalOutput.toJV))), ("change", some (.arr (o.change.map (ofInt ·.toNat))))]

/-- Decodes, then validates (an invalid breakdown is `invalidBundle`, thrown through the decoder). -/
def Outputs.ofJV (v : JV) : D Outputs := do
  let kvs ← asObject v
  let external := (← keyIfPresent kvs "external" (asArray ExternalOutput.ofJV)).getD #[]
  let change := (← keyIfPresent kvs "change" (asArray asUInt32)).getD #[]
  let o : Outputs := { external, change }
  match o.validate with
  | .ok () => return o
  | .error e => throw e.name

/-- `transaction()` with its errors whole: a `WalletError` (`.inl`, reasons included) or the transaction
decoder's case name (`.inr`). The breakdown is checked, then the stored payment against the txid, the
monetary range and the breakdown. -/
def checkedTransaction (h : HistoryEntry) : Except (WalletError ⊕ String) (Option Transaction) := do
  if let some o := h.outputs then o.validate.mapError .inl
  let some raw := h.rawTransaction | return none
  let tx ← (Transaction.decode raw).mapError (.inr ·.name)
  unless tx.txid == h.txid do throw (.inl (.invalidBundle "payment details do not match the transaction ID"))
  let mut total : Int64 := 0
  for o in tx.outputs do
    unless 0 ≤ o.value && o.value ≤ bitcoinAmountMaximum && o.value ≤ bitcoinAmountMaximum - total do
      throw (.inl .invalidTransactionAmounts)
    total := total + o.value
  if let some o := h.outputs then (o.validateAgainst tx).mapError .inl
  return some tx

/-- `transaction()`, failing with the error's case name. -/
def transaction (h : HistoryEntry) : Except String (Option Transaction) :=
  h.checkedTransaction.mapError fun | .inl e => e.name | .inr n => n

def toJV (h : HistoryEntry) : JV :=
  obj [("txid", some (.str (displayHex h.txid))), ("height", some (ofInt h.height.toNat)),
    ("received", some (ofInt h.received.toInt)), ("spent", some (ofInt h.spent.toInt)),
    ("fee", h.fee.map (ofInt ·.toInt)), ("replacedBy", h.replacedBy.map (.str ∘ displayHex)),
    ("rawTransaction", h.rawTransaction.map ofData),
    ("fundingScripts", if h.fundingScripts.isEmpty then none else some (.arr (h.fundingScripts.map ofData))),
    ("blockHash", h.blockHash.map (.str ∘ displayHex)), ("outputs", h.outputs.map Outputs.toJV)]

def ofJV (v : JV) : D HistoryEntry := do
  let kvs ← asObject v
  let txid ← hexField kvs "txid"
  let replacedBy ← match ← keyIfPresent kvs "replacedBy" asString with
    | none => pure none
    | some s => match Wire.dataOfHex? s with
      | some b => pure (some (ByteArray.reverse b))
      | none => dataCorrupted
  let height ← key kvs "height" asUInt32
  let blockHash ← match ← keyIfPresent kvs "blockHash" asString with
    | none => pure none
    | some s => match Wire.dataOfHex? s with
      | some b => if b.size == 32 && height > 0 then pure (some (ByteArray.reverse b)) else dataCorrupted
      | none => dataCorrupted
  let received ← key kvs "received" asInt64
  let spent ← key kvs "spent" asInt64
  let fee ← keyIfPresent kvs "fee" asInt64
  let rawTransaction ← keyIfPresent kvs "rawTransaction" asData
  let fundingScripts := (← keyIfPresent kvs "fundingScripts" (asArray asData)).getD #[]
  let outputs ← keyIfPresent kvs "outputs" Outputs.ofJV
  let h : HistoryEntry := { txid := ByteArray.reverse txid, height, received, spent, fee, replacedBy, rawTransaction,
                            fundingScripts, blockHash, outputs }
  discard h.transaction
  return h
end HistoryEntry

namespace PendingSend
def toJV (p : PendingSend) : JV :=
  obj [("rawTransaction", some (.str (hex p.rawTransaction))), ("selected", some (.arr (p.selected.map WalletUTXO.toJV))),
    ("changeIndex", p.changeIndex.map (ofInt ·.toNat)), ("changeOutputIndex", p.changeOutputIndex.map (ofInt ·.toNat)),
    ("fee", some (ofInt p.fee.toInt))]

def ofJV (v : JV) : D PendingSend := do
  let kvs ← asObject v
  let rawHex ← key kvs "rawTransaction" asString
  let raw ← match Wire.dataOfHex? rawHex with
    | some b => if (Transaction.decode b).toOption.isSome then pure b else dataCorrupted
    | none => dataCorrupted
  let selected ← key kvs "selected" (asArray WalletUTXO.ofJV)
  let changeIndex ← keyIfPresent kvs "changeIndex" asUInt32
  let changeOutputIndex ← keyIfPresent kvs "changeOutputIndex" asUInt32
  let fee ← key kvs "fee" asInt64
  return { rawTransaction := raw, selected, changeIndex, changeOutputIndex, fee }
end PendingSend

namespace WalletState

def toJV (s : WalletState) : JV :=
  obj [("descriptor", some (.str s.descriptor)), ("network", some (.str s.network)),
    ("creationHeight", some (ofInt s.creationHeight.toNat)), ("nextReceiveIndex", some (ofInt s.nextReceiveIndex.toNat)),
    ("nextChangeIndex", some (ofInt s.nextChangeIndex.toNat)), ("nextScanHeight", some (ofInt s.nextScanHeight.toNat)),
    ("scannedThroughHash", s.scannedThroughHash.map (.str ∘ displayHex)),
    ("utxos", some (.arr (s.allUtxos.map WalletUTXO.toJV))), ("history", some (.arr (s.history.map HistoryEntry.toJV))),
    ("observedFeeRates", some (.arr (s.observedFeeRates.map ofDouble))),
    ("pendingSends", some (.arr (s.pendingSends.map PendingSend.toJV)))]

/-- Every coin well-formed and no outpoint twice; optionally the total within the monetary range. -/
def validateCoins (coins : Array WalletUTXO) (countingTotal : Bool := true) : D Unit := do
  let mut seen : Array Transaction.Outpoint := #[]
  let mut total : Int := 0
  for c in coins do
    unless c.txid.size == 32 && !c.scriptPubKey.isEmpty && c.amount > 0 && c.amount ≤ bitcoinAmountMaximum &&
        (c.spent.map (·.spentBy.size == 32)).getD true && !seen.contains c.outpoint do dataCorrupted
    seen := seen.push c.outpoint
    if !countingTotal then continue
    let next := total + c.amount.toInt
    unless next ≤ bitcoinAmountMaximum.toInt do dataCorrupted
    total := next

def inMoney (v : Int64) : Bool := 0 ≤ v && v ≤ bitcoinAmountMaximum

def ofJV (v : JV) : D WalletState := do
  let kvs ← asObject v
  let descriptor ← key kvs "descriptor" asString
  let network ← key kvs "network" asString
  let creationHeight ← key kvs "creationHeight" asUInt32
  let nextReceiveIndex ← key kvs "nextReceiveIndex" asUInt32
  let nextChangeIndex ← key kvs "nextChangeIndex" asUInt32
  -- A cursor the gap-limit lookahead cannot derive from is damage, not a loop to trap in.
  let maximum : UInt32 := 0x8000_0000 - Wallet.gapLimit
  unless nextReceiveIndex ≤ maximum && nextChangeIndex ≤ maximum do dataCorrupted
  let nextScanHeight ← key kvs "nextScanHeight" asUInt32
  let scannedThroughHash ← match ← keyIfPresent kvs "scannedThroughHash" asString with
    | none => pure none
    | some s => match Wire.dataOfHex? s with
      | some b => if b.size == 32 && nextScanHeight > 0 then pure (some (ByteArray.reverse b)) else dataCorrupted
      | none => dataCorrupted
  let allUtxos ← key kvs "utxos" (asArray WalletUTXO.ofJV)
  let history ← key kvs "history" (asArray HistoryEntry.ofJV)
  let observedFeeRates := (← keyIfPresent kvs "observedFeeRates" (asArray asDouble)).getD #[]
  let pendingSends := (← keyIfPresent kvs "pendingSends" (asArray PendingSend.ofJV)).getD #[]
  let s : WalletState :=
    { descriptor := descriptor, network := network, creationHeight := creationHeight,
      nextReceiveIndex := nextReceiveIndex, nextChangeIndex := nextChangeIndex, nextScanHeight := nextScanHeight,
      scannedThroughHash := scannedThroughHash, allUtxos := allUtxos, history := history, observedFeeRates := observedFeeRates, pendingSends := pendingSends }
  validateCoins allUtxos (countingTotal := false)
  validateCoins s.utxos
  for p in pendingSends do
    validateCoins p.selected
    unless inMoney p.fee do dataCorrupted
  unless history.all (fun e => e.txid.size == 32 && inMoney e.received && inMoney e.spent &&
      (e.fee.map inMoney).getD true) &&
    observedFeeRates.all (fun r => r.isFinite && r > 0 && r ≤ 10_000) do dataCorrupted
  return s

/-- The wallet file text (`JSONEncoder` output, keys sorted). A non-finite fee sample cannot be
written: `JSONEncoder` throws `EncodingError.invalidValue` (`invalidValue` here). -/
def encode (s : WalletState) : Except String String := do
  unless s.observedFeeRates.all (·.isFinite) do throw "invalidValue"
  return write s.toJV

/-- `JSONDecoder().decode(WalletState.self, from:)`. -/
def decode (text : String) : D WalletState := decodeText text ofJV

end WalletState
end Winnow
