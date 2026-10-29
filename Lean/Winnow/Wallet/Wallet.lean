import Winnow.Wallet.ImportBundle
import Winnow.Wallet.HistoryLedger
import Winnow.Wallet.CoinSelection
import Winnow.Wallet.Descriptor
import Winnow.Wallet.PSBTRoles
import Winnow.Keys.BIP39
import Winnow.Keys.BIP86
import Winnow.Keys.KeyStore
import Winnow.Keys.SilentPayments
import Winnow.Tx.FundingSources
import Winnow.Net.FilterSync
import Std.Sync.Mutex

/-! # The single-sig wallet (port of `actor Wallet` in `Sources/WalletCore/Wallet/Wallet.swift`, plus
`Wallet.importing` / `verifyImport` from `ImportBundle.swift`)

The Swift actor becomes a structure whose mutable state is an `IO.Ref WalletState`; every method is an
`IO` action (`WM`, failing with the Swift error's case). Operations that Swift writes as "persist a
candidate, then adopt it" do exactly that here; the two that mutate first and persist after
(`recordScanHeight`, and `freshReceiveAddress`, which restores the index on failure) keep that order.
The wallet file is written atomically (temporary file in the same directory, then rename) with sorted
keys (the Swift `JSONEncoder()` uses a per-process hash order; the bytes otherwise agree).

Randomness — the fresh mnemonic's entropy, the anti-fee-sniping draws, the change position, BIP340
auxiliary randomness — comes from an injectable `Randomness`, so a test can pin every draw. The secret
store is the `Keys` `KeyStore` interface over `IO` (the Keychain capability on iOS).

`verifyImport` is generic over a `ScanSource` (what it needs of `FilterSync`); the network-driven source is
the I/O area's. -/

namespace Winnow
open Keys SwiftJSON
open Tx (BitcoinNetwork)

/-! ## Failures -/

/-- Every failure a wallet operation surfaces, by the Swift error it mirrors. -/
inductive WalletFailure where
  | wallet (e : WalletError)
  | feeBump (e : FeeBumpError)
  /-- An error of another module, by its case name (`insufficientFunds`, `notFound`, `keyNotFound`, …). -/
  | named (name : String)
  | io (e : IO.Error)
  deriving Inhabited

def WalletFailure.name : WalletFailure → String
  | .wallet e => e.name | .feeBump e => e.name | .named n => n | .io _ => "ioError"

abbrev WM := ExceptT WalletFailure IO

def WM.liftE {ε α} (name : ε → String) (r : Except ε α) : WM α :=
  match r with | .ok a => pure a | .error e => throw (.named (name e))

def WM.wallet {α} (r : Except WalletError α) : WM α :=
  match r with | .ok a => pure a | .error e => throw (.wallet e)

def WM.io {α} (x : IO α) : WM α := ExceptT.mk do
  try return .ok (← x) catch e => return .error (.io e)

/-- A keyed-store call, with `KeyStoreError`'s case name. -/
def WM.keys {α} (x : ExceptT KeyStoreError IO α) : WM α := do
  match ← WM.io x.run with
  | .ok a => pure a
  | .error e => throw (.named e.name)

/-! ## Injectable randomness -/

structure Randomness where
  /-- 16 bytes of mnemonic entropy for `create`. -/
  entropy : IO ByteArray
  /-- One draw in `0 ..< 1` for the anti-fee-sniping locktime (`Double.random(in: 0 ..< 1)`). -/
  draw : IO Float
  /-- The change output's position among `n` payments: uniform in `0 ... n`. -/
  changePosition : Nat → IO Nat
  /-- 32 bytes of BIP340 auxiliary randomness per signature. -/
  auxRand : IO ByteArray

def randomUInt64 : IO UInt64 := do
  let b ← IO.getRandomBytes 8
  return (List.range 8).foldl (fun a i => (a <<< 8) ||| b[i]!.toUInt64) 0

def Randomness.system : Randomness where
  entropy := IO.getRandomBytes 16
  draw := do return ((← randomUInt64) >>> 11).toFloat / (2 ^ 53 : Float)
  changePosition n := do return ((← randomUInt64) % (n + 1).toUInt64).toNat
  auxRand := IO.getRandomBytes 32

/-! ## An in-memory key store over a reference -/

/-- `InMemoryKeyStore` (Tests/Support) as an `IO` store: IDs compare by canonical equivalence (NFD). -/
def inMemoryKeyStore (ref : IO.Ref InMemorySecrets) : KeyStore IO where
  store secret id := do
    let k := Unicode.nfd id
    if (← ref.get).contains k then throw (.alreadyExists id)
    ref.modify (·.insert k secret)
  load id := do
    match (← ref.get)[Unicode.nfd id]? with
    | some s => pure s
    | none => throw (.notFound id)
  delete id := ref.modify (·.erase (Unicode.nfd id))

/-! ## The wallet -/

structure Wallet where
  id : String
  network : BitcoinNetwork
  descriptor : Descriptor
  /-- Neutered account key at m/86'/coin'/account'. -/
  accountKey : HDKey
  keyStore : KeyStore IO
  storagePath : Option System.FilePath
  random : Randomness
  stateRef : IO.Ref WalletState
  /-- Derived outputs per index (a pure function of the descriptor, kept because derivation is costly). -/
  derivedCache : IO.Ref (Std.HashMap UInt32 (Array Descriptor.DerivedOutput))
  /-- Serialises `advanceCursors` (the Swift actor's guarantee): concurrent reservations keep each chain's
  highest cursor instead of the last writer's. -/
  cursorLock : Std.Mutex Unit

/-- A fully signed send whose selection is not yet committed. -/
structure PreparedSend where
  built : BuiltTransaction
  /-- The silent payments with their derived P2TR scripts, in the order given; the review gate binds them
  (only the wallet can derive them: it needs the selected inputs' keys). -/
  resolvedSilentPayments : Array Payment := #[]
  /-- Their codes, encoded, for the history. -/
  silentPaymentAddresses : Array String := #[]
  selected : Array WalletUTXO
  change : Option Payment
  changeIndex : UInt32
  changeOutputIndex : Option UInt32
  fee : Int64
  deriving Inhabited

/-- A replacement whose wallet mutation waits for the broadcaster. -/
structure PreparedFeeBump where
  originalTxid : ByteArray
  built : BuiltTransaction
  selected : Array WalletUTXO
  originalChangeOutputIndex : UInt32
  change : Option Payment
  changeIndex : UInt32
  changeOutputIndex : Option UInt32
  deriving Inhabited

/-- What `verifyImport` needs of `FilterSync`: its frontier before and after, and a scan that hands every
matched block to the callback. -/
structure ScanSource where
  nextScanHeight : IO UInt32
  lastScannedHeight : IO (Option UInt32)
  sync : Array ByteArray → (Net.BlockMatch → WM Unit) → WM Unit

namespace Wallet

def spentCoinHorizon : UInt32 := 100
def maximumStateBytes : Nat := 64 * 1024 * 1024
def incrementalRelayFeeSatPerVByte : Float := 1.0

def coinType (n : BitcoinNetwork) : UInt32 := if n == .mainnet then 0 else 1
def hdNetwork (n : BitcoinNetwork) : HDKey.Network := if n == .mainnet then .mainnet else .testnet
def networkName : BitcoinNetwork → String
  | .mainnet => "mainnet" | .signet => "signet" | .regtest => "regtest"

def walletDerivation : Array Descriptor.Element := #[.multipath #[0, 1], .wildcard false]

/-- The canonical multipath `tr()` descriptor for an account key. -/
def makeDescriptor (accountKey : HDKey) (origin : Descriptor.KeyOrigin) (network : BitcoinNetwork) : Descriptor :=
  { expression := .tr { origin := some origin, base := .extended accountKey.neutered (hdNetwork network),
                        derivation := { elements := walletDerivation } } }

/-- Validates the wallet descriptor shape and returns its key origin. -/
def origin (d : Descriptor) : Except WalletError Descriptor.KeyOrigin := do
  let bad : WalletError := .invalidDescriptor "expected tr([fp/86'/c'/a']xpub/<0;1>/*)"
  let .tr key := d.expression | throw bad
  let some o := key.origin | throw bad
  unless key.derivation.elements == walletDerivation do throw bad
  if let .extended account _ := key.base then
    if account.depth > 253 then
      throw (.invalidDescriptor s!"account key at depth {account.depth} has no room for <0;1>/*")
  return o

def hex8 (n : UInt32) : String :=
  let h := String.ofList (Nat.toDigits 16 n.toNat)
  String.ofList (List.replicate (8 - h.length) '0') ++ h

def make (network : BitcoinNetwork) (descriptor : Descriptor) (accountKey : HDKey) (keyStore : KeyStore IO)
    (storagePath : Option System.FilePath) (random : Randomness) (state : WalletState) : WM Wallet := do
  let o ← WM.wallet (origin descriptor)
  return { id := hex8 o.fingerprint, network, descriptor, accountKey, keyStore, storagePath, random,
           stateRef := ← IO.mkRef state, derivedCache := ← IO.mkRef {}, cursorLock := ← Std.Mutex.new () }

/-! ### Persistence -/

/-- Write `text` to `path` atomically: a temporary file beside it, then a rename over it. -/
def writeAtomically (path : System.FilePath) (text : String) : IO Unit := do
  let name := path.fileName.getD "wallet.json"
  let tmp := path.withFileName s!".{name}.{hex (← IO.getRandomBytes 6)}.tmp"
  try
    IO.FS.writeFile tmp text
    IO.FS.rename tmp path
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw e

def encodeState (s : WalletState) : WM String :=
  WM.liftE (fun (e : String) => e) s.encode

def persistState (path : Option System.FilePath) (s : WalletState) : WM Unit := do
  let some p := path | return
  let text ← encodeState s
  WM.io (writeAtomically p text)

def persist (w : Wallet) (candidate : WalletState) : WM Unit := persistState w.storagePath candidate

def state (w : Wallet) : IO WalletState := w.stateRef.get

/-! ### Creation / opening -/

/-- Creates a fresh wallet: a new 12-word mnemonic stored in the key store and an empty state scanning
forward from `creationHeight`. A failed write removes the key-store entry again. -/
def create (network : BitcoinNetwork) (keyStore : KeyStore IO) (storagePath : Option System.FilePath := none)
    (entropy : Option ByteArray := none) (creationHeight : UInt32 := 0) (account : UInt32 := 0)
    (random : Randomness := .system) : WM Wallet := do
  let entropy ← match entropy with | some e => pure e | none => WM.io random.entropy
  let mnemonic ← WM.liftE (·.name) (BIP39.mnemonic entropy)
  let master ← WM.liftE (·.name) (HDKey.ofSeed (BIP39.seed mnemonic))
  let ct := coinType network
  let accountKey ← WM.liftE (·.name) (BIP86.accountKey master ct account)
  let o : Descriptor.KeyOrigin := { fingerprint := master.fingerprint, path := #[86, ct, account].map (· + HDKey.hardenedOffset) }
  let descriptor := makeDescriptor accountKey o network
  let state : WalletState := { descriptor := descriptor.serialized, network := networkName network, creationHeight,
                               nextScanHeight := creationHeight }
  let w ← make network descriptor accountKey.neutered keyStore storagePath random state
  WM.keys (keyStore.store (.mnemonic mnemonic) w.id)
  tryCatchThe WalletFailure (persistState storagePath state) fun e => do
    discard <| WM.io (keyStore.delete w.id).run
    throw e
  return w

/-- `create(accountKey:masterFingerprint:…)`: a wallet from the private key at m/86'/coin'/account' and its
master fingerprint, without a root key or recovery words. The key's shape is checked (private, as deep as
the path, ending at its last step); a child key alone cannot prove the claimed ancestry. -/
def createFromAccountKey (accountKey : HDKey) (masterFingerprint : UInt32) (network : BitcoinNetwork)
    (keyStore : KeyStore IO) (storagePath : Option System.FilePath := none) (creationHeight : UInt32 := 0)
    (account : UInt32 := 0) (random : Randomness := .system) : WM Wallet := do
  unless account < HDKey.hardenedOffset do throw (.named "invalidPath")
  let path := #[86, coinType network, account].map (· + HDKey.hardenedOffset)
  unless accountKey.isPrivate && accountKey.depth.toNat == path.size && some accountKey.childIndex == path.back? do
    throw (.wallet .accountKeyMismatch)
  let o : Descriptor.KeyOrigin := { fingerprint := masterFingerprint, path }
  let descriptor := makeDescriptor accountKey o network
  let state : WalletState := { descriptor := descriptor.serialized, network := networkName network, creationHeight,
                               nextScanHeight := creationHeight }
  let w ← make network descriptor accountKey.neutered keyStore storagePath random state
  WM.keys (keyStore.store (.accountKey (accountKey.serialized (hdNetwork network)) masterFingerprint) w.id)
  tryCatchThe WalletFailure (persistState storagePath state) fun e => do
    discard <| WM.io (keyStore.delete w.id).run
    throw e
  return w

/-- Re-opens a wallet from its persisted state (size ceiling measured before reading). -/
def «open» (storagePath : System.FilePath) (keyStore : KeyStore IO) (random : Randomness := .system) : WM Wallet := do
  let size ← WM.io do return (← storagePath.metadata).byteSize
  if size.toNat > maximumStateBytes then throw (.wallet (.storageTooLarge maximumStateBytes))
  let data ← WM.io (IO.FS.readBinFile storagePath)
  if data.size > maximumStateBytes then throw (.wallet (.storageTooLarge maximumStateBytes))
  let some text := String.fromUTF8? data | throw (.named "dataCorrupted")
  let state ← match WalletState.decode text with
    | .ok s => pure s
    | .error e => throw (if e == "unsupportedWalletData" then .wallet .unsupportedWalletData else .named e)
  let some network := BitcoinNetwork.ofString? state.network
    | throw (.wallet (.invalidBundle s!"unknown network {ImportBundle.excerpt state.network}"))
  let descriptor ← WM.liftE (·.name) (Descriptor.parse state.descriptor)
  discard <| WM.wallet (origin descriptor)
  let .tr key := descriptor.expression | throw (.wallet (.invalidDescriptor state.descriptor))
  let .extended accountKey _ := key.base | throw (.wallet (.invalidDescriptor state.descriptor))
  make network descriptor accountKey.neutered keyStore (some storagePath) random state

/-! ### Reading -/

def creationHeight (w : Wallet) : IO UInt32 := return (← w.state).creationHeight
def nextScanHeight (w : Wallet) : IO UInt32 := return (← w.state).nextScanHeight
def nextReceiveIndex (w : Wallet) : IO UInt32 := return (← w.state).nextReceiveIndex
def nextChangeIndex (w : Wallet) : IO UInt32 := return (← w.state).nextChangeIndex
def utxos (w : Wallet) : IO (Array WalletUTXO) := return (← w.state).utxos
def allUtxos (w : Wallet) : IO (Array WalletUTXO) := return (← w.state).allUtxos
def history (w : Wallet) : IO (Array HistoryEntry) := return (← w.state).history
def observedFeeRates (w : Wallet) : IO (Array Float) := return (← w.state).observedFeeRates
def balance (w : Wallet) : IO Int64 := return (← w.utxos).foldl (fun a u => a + u.amount) 0

/-- Coinbase outputs need 100 confirmations at the last scanned height. -/
def isMature (s : WalletState) (u : WalletUTXO) : Bool :=
  if !u.isCoinbase then true
  else
    let tip := if s.nextScanHeight == 0 then 0 else s.nextScanHeight - 1
    tip ≥ u.height && tip - u.height ≥ coinbaseMaturity - 1

def spendableUtxosOf (s : WalletState) : Array WalletUTXO := s.utxos.filter (isMature s)
def spendableUtxos (w : Wallet) : IO (Array WalletUTXO) := return spendableUtxosOf (← w.state)

def pendingTx (p : PendingSend) : Option Transaction := (Transaction.decode p.rawTransaction).toOption
def pendingTxid (p : PendingSend) : Option ByteArray := (pendingTx p).map (·.txid)

/-- Pending sends a same-input fee bump can act on. -/
def feeBumpableTxids (w : Wallet) : IO (Array ByteArray) := do
  let s ← w.state
  return s.pendingSends.filterMap fun p => do
    let _ ← p.changeIndex
    let txid ← pendingTxid p
    let vout ← p.changeOutputIndex
    if s.utxos.any (fun u => u.txid == txid && u.vout == vout) then some txid else none

/-! ### Addresses -/

def derivedAt (w : Wallet) (chain : AddressChain) (index : UInt32) : WM Descriptor.DerivedOutput := do
  let outs ← match (← w.derivedCache.get)[index]? with
    | some outs => pure outs
    | none =>
      let outs ← WM.liftE (·.name) (w.descriptor.derived index w.network)
      w.derivedCache.modify (·.insert index outs)
      pure outs
  let some o := outs[chain.rawValue]? | throw (.named "indexOutOfRange")
  return o

def scriptPubKey (w : Wallet) (chain : AddressChain) (index : UInt32) : WM ByteArray :=
  return (← w.derivedAt chain index).scriptPubKey

def address (w : Wallet) (chain : AddressChain) (index : UInt32) : WM String :=
  return (← w.derivedAt chain index).address

/-- The next unused receive address; advances (and persists) the index, restoring it on failure. -/
def freshReceiveAddress (w : Wallet) : WM String := do
  let s ← w.state
  let a ← w.address .receive s.nextReceiveIndex
  let previous := s.nextReceiveIndex
  w.stateRef.modify fun s => { s with nextReceiveIndex := s.nextReceiveIndex + 1 }
  tryCatchThe WalletFailure (do w.persist (← w.state)) fun e => do
    w.stateRef.modify fun s => { s with nextReceiveIndex := previous }
    throw e
  return a

/-- Watched scriptPubKey ↦ owning (chain, index): used indices plus the gap-limit lookahead. -/
def watchMap (w : Wallet) (s : WalletState) : WM (Std.HashMap ByteArray (AddressChain × UInt32)) := do
  let mut map : Std.HashMap ByteArray (AddressChain × UInt32) := {}
  for chain in [AddressChain.receive, .change] do
    let next := if chain == .receive then s.nextReceiveIndex else s.nextChangeIndex
    for i in [0:(next + gapLimit).toNat] do
      map := map.insert (← w.scriptPubKey chain i.toUInt32) (chain, i.toUInt32)
  return map

/-- Every watched scriptPubKey (the lookahead window and every known coin's script, spent rows
included). Order carries no meaning (a `Set` in Swift). -/
def watchScripts (w : Wallet) : WM (Array ByteArray) := do
  let s ← w.state
  let mut set : Std.HashSet ByteArray := {}
  for (k, _) in (← w.watchMap s).toList do set := set.insert k
  for u in s.allUtxos do set := set.insert u.scriptPubKey
  return set.toArray

/-! ### Scanning -/

def pruneSpentCoins (s : WalletState) (nextScanHeight : UInt32) : WalletState :=
  if nextScanHeight ≤ spentCoinHorizon then s
  else
    let cutoff := nextScanHeight - spentCoinHorizon
    { s with allUtxos := s.allUtxos.filter fun u => match u.spent with
        | some { height := some h, .. } => !(h < cutoff)
        | _ => true }

/-- Mirrors FilterSync's frontier into the persisted state (mutates, then persists — as Swift).
`scannedThroughHash` is the hash of block `nextScanHeight - 1`; without it the stored hash is cleared,
never left describing another height. (Swift's precondition — 32 bytes and a positive height — is a
trap there; here such a hash is not recorded.) -/
def recordScanHeight (w : Wallet) (nextScanHeight : UInt32) (scannedThroughHash : Option ByteArray := none) : WM Unit := do
  let hash := scannedThroughHash.filter fun h => h.size == 32 && nextScanHeight > 0
  w.stateRef.modify fun s => pruneSpentCoins { s with nextScanHeight, scannedThroughHash := hash } nextScanHeight
  w.persist (← w.state)

def scannedThroughHash (w : Wallet) : IO (Option ByteArray) := return (← w.state).scannedThroughHash

/-- Reserves every address below the supplied cursors (neither moves backwards), persisting both before
the live state changes. Cursors must leave room for the gap-limit lookahead (`invalidPath`). -/
def advanceCursors (w : Wallet) (nextReceiveIndex nextChangeIndex : Option UInt32 := none) : WM Unit :=
  w.cursorLock.atomically (m := WM) do
    let s ← w.state
    let candidate := { s with nextReceiveIndex := max s.nextReceiveIndex (nextReceiveIndex.getD 0),
                              nextChangeIndex := max s.nextChangeIndex (nextChangeIndex.getD 0) }
    let maximum := HDKey.hardenedOffset - gapLimit
    unless candidate.nextReceiveIndex ≤ maximum && candidate.nextChangeIndex ≤ maximum do throw (.named "invalidPath")
    if candidate.nextReceiveIndex == s.nextReceiveIndex && candidate.nextChangeIndex == s.nextChangeIndex then return
    w.persist candidate
    w.stateRef.set candidate

/-- The wallet's history entry index for `txid`. -/
def historyIndex (s : WalletState) (txid : ByteArray) : Option Nat := s.history.findIdx? (·.txid == txid)

/-- A replacement chain's ancestor confirming discards every descendant (coins, pending records, history). -/
def reconcileReplacementDescendants (s : WalletState) (txid : ByteArray) : WalletState × Array ByteArray := Id.run do
  let some root := historyIndex s txid | return (s, #[])
  if s.history[root]!.replacedBy.isNone then return (s, #[])
  let mut descendants : Array ByteArray := #[]
  let mut next := s.history[root]!.replacedBy
  let mut fuel := s.history.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    match next with
    | some t =>
      if descendants.contains t then break
      descendants := descendants.push t
      next := (s.history.find? (·.txid == t)).bind (·.replacedBy)
    | none => break
  let history := s.history.modify root fun e => { e with replacedBy := none }
  let s := { s with
    history := history.filter fun e => !descendants.contains e.txid
    allUtxos := s.allUtxos.filter fun u => !descendants.contains u.txid
    pendingSends := s.pendingSends.filter fun p => !((pendingTxid p).map descendants.contains).getD false }
  return (s, descendants)

/-- A pending send with exactly the confirmed transaction's inputs (as a multiset) lost the race:
its outputs are removed and its history row marked replaced. -/
def reconcilePendingConflict (s : WalletState) (tx : Transaction) : WalletState × Option PendingSend := Id.run do
  let confirmedInputs := tx.inputs.map (·.previousOutput)
  let txid := tx.txid
  let isConflict (p : PendingSend) : Bool := Id.run do
    let some candidate := pendingTx p | return false
    if candidate.txid == txid then return false
    let mut unmatched := confirmedInputs
    for i in candidate.inputs do
      match unmatched.findIdx? (· == i.previousOutput) with
      | some k => unmatched := unmatched.eraseIdx! k
      | none => return false
    return unmatched.isEmpty
  let some k := s.pendingSends.findIdx? isConflict | return (s, none)
  let pending := s.pendingSends[k]!
  let s := { s with pendingSends := s.pendingSends.eraseIdx! k }
  let some pendingTxid' := pendingTxid pending | return (s, some pending)
  let s := { s with allUtxos := s.allUtxos.filter (·.txid != pendingTxid') }
  let s := match historyIndex s pendingTxid' with
    | some h => { s with history := s.history.modify h fun e => { e with replacedBy := some txid } }
    | none => s
  return (s, some pending)

/-- Bitcoin's output-value rules for every transaction of the block. -/
def checkBlockAmounts (b : Net.Block) : Except WalletError Unit := do
  for tx in b.transactions do
    let mut total : Int := 0
    for o in tx.outputs do
      unless o.value ≥ 0 && o.value ≤ bitcoinAmountMaximum do throw .invalidTransactionAmounts
      total := total + o.value.toInt
      unless total ≤ bitcoinAmountMaximum.toInt do throw .invalidTransactionAmounts

def confirmPendingTombstone (s : WalletState) (input : Transaction.Input) (txid : ByteArray) (height : UInt32) : WalletState :=
  match s.allUtxos.findIdx? (fun u => match u.spent with
      | some m => m.height.isNone && u.txid == input.previousOutput.txid && u.vout == input.previousOutput.vout
      | none => false) with
  | some k => { s with allUtxos := s.allUtxos.modify k fun u => { u with spent := some { spentBy := txid, height := some height } } }
  | none => s

/-- Tombstones every input spending one of our live coins; what left, and whether every input was ours. -/
def applySpends (s : WalletState) (tx : Transaction) (txid : ByteArray) (height : UInt32) (effect : MatchEffect) :
    WalletState × MatchEffect × Int64 × Bool := Id.run do
  let mut s := s
  let mut effect := effect
  let mut spent : Int64 := 0
  let mut allOurs := !tx.inputs.isEmpty
  for input in tx.inputs do
    match s.allUtxos.findIdx? (fun u => !u.isSpent && u.txid == input.previousOutput.txid && u.vout == input.previousOutput.vout) with
    | none =>
      s := confirmPendingTombstone s input txid height
      allOurs := false
    | some k =>
      s := { s with allUtxos := s.allUtxos.modify k fun u => { u with spent := some { spentBy := txid, height := some height } } }
      let u := s.allUtxos[k]!
      spent := spent + u.amount
      effect := { effect with spent := effect.spent.push { txid := u.txid, vout := u.vout, spentBy := txid, height := height } }
  return (s, effect, spent, allOurs)

/-- Admits every watched, positive output as a coin (or re-heights a known one) and advances the
gap-limit bookkeeping. -/
def applyOutputs (s : WalletState) (tx : Transaction) (txid : ByteArray) (map : Std.HashMap ByteArray (AddressChain × UInt32))
    (height : UInt32) (isCoinbase : Bool) (effect : MatchEffect) : WalletState × MatchEffect × Int64 := Id.run do
  let mut s := s
  let mut effect := effect
  let mut received : Int64 := 0
  for h : vout in [0:tx.outputs.size] do
    let output := tx.outputs[vout]
    if !(output.value > 0) then continue
    let some (chain, index) := map[output.scriptPubKey]? | continue
    match s.allUtxos.findIdx? (fun u => u.txid == txid && u.vout == vout.toUInt32) with
    | some k =>
      let refound := s.allUtxos[k]!.height == 0 && !s.history.any (·.txid == txid)
      s := { s with allUtxos := s.allUtxos.modify k fun u => { u with height } }
      if refound then
        received := received + output.value
        effect := { effect with received := effect.received.push s.allUtxos[k]! }
    | none =>
      let u : WalletUTXO := { txid := txid, vout := vout.toUInt32, amount := output.value, scriptPubKey := output.scriptPubKey,
                              chain := chain, index := index, height := height, isCoinbase := isCoinbase }
      s := { s with allUtxos := s.allUtxos.push u }
      received := received + output.value
      effect := { effect with received := effect.received.push u }
      if chain == .receive && index ≥ s.nextReceiveIndex then s := { s with nextReceiveIndex := index + 1 }
      if chain == .change && index ≥ s.nextChangeIndex then s := { s with nextChangeIndex := index + 1 }
  return (s, effect, received)

/-- Confirms the transaction into history through `HistoryLedger` (a known pending send confirms in place,
anything else is appended), retires its pending record, and samples the feerate when the fee is exact:
only when every input was ours. -/
def recordConfirmedHistory (s : WalletState) (tx : Transaction) (txid : ByteArray) (height : UInt32) (blockHash : ByteArray)
    (received spent : Int64) (feeIsExact : Bool) : WalletState := Id.run do
  let mut s := s
  let fee := HistoryLedger.exactFee spent tx feeIsExact
  if let some fee := fee then
    let vsize := TransactionBuilder.vsize tx
    if vsize > 0 then
      let rates := s.observedFeeRates.push (Float.ofInt fee.toInt / vsize.toFloat)
      s := { s with observedFeeRates := if rates.size > 20 then rates.eraseIdx! 0 else rates }
  s := { s with history := (HistoryLedger.record s.history tx txid height blockHash received spent fee).1 }
  return { s with pendingSends := s.pendingSends.filter fun p => pendingTxid p != some txid }

def checkWalletTotalInvariant (s : WalletState) : Except WalletError Unit := do
  let mut total : Int := 0
  for c in s.utxos do
    total := total + c.amount.toInt
    unless c.amount > 0 && c.amount ≤ bitcoinAmountMaximum && total ≤ bitcoinAmountMaximum.toInt do
      throw .invalidTransactionAmounts

def isCoinbaseTx (tx : Transaction) : Bool :=
  match tx.inputs[0]? with
  | some i => i.previousOutput.txid == ByteArray.mk (Array.replicate 32 0) && i.previousOutput.vout == 0xFFFF_FFFF
  | none => false

/-- Consumes one matched block as one state transition (validated first, persisted before adopted). -/
def apply (w : Wallet) (m : Net.BlockMatch) : WM MatchEffect := do
  WM.wallet (checkBlockAmounts m.block)
  let s0 ← w.state
  let map ← w.watchMap s0
  let mut s := s0
  let mut effect : MatchEffect := {}
  for tx in m.block.transactions do
    let txid := tx.txid
    let (s1, discarded) := reconcileReplacementDescendants s txid
    s := s1
    effect := { effect with discardedReplacements := effect.discardedReplacements ++ discarded }
    let (s2, conflicting) := reconcilePendingConflict s tx
    s := s2
    if let some c := conflicting then
      if let some t := pendingTxid c then
        effect := { effect with discardedReplacements := effect.discardedReplacements.push t }
    let coinbase := isCoinbaseTx tx
    let mut spentAmount : Int64 := 0
    let mut allOurs := !coinbase && !tx.inputs.isEmpty
    if !coinbase then
      let (s3, e3, sp, ao) := applySpends s tx txid m.height effect
      s := s3; effect := e3; spentAmount := sp; allOurs := ao
    if conflicting.isSome then allOurs := true
    let (s4, e4, received) := applyOutputs s tx txid map m.height coinbase effect
    s := s4; effect := e4
    let accounted := match conflicting with
      | some c => c.selected.foldl (fun a u => a + u.amount) 0
      | none => spentAmount
    let touches := spentAmount > 0 || received > 0 || conflicting.isSome || s.history.any (·.txid == txid)
    if !touches then continue
    s := recordConfirmedHistory s tx txid m.height m.blockHash received accounted allOurs
  WM.wallet (checkWalletTotalInvariant s)
  w.persist s
  w.stateRef.set s
  return effect

/-- Enrich an existing receipt with its transaction, without replaying its effects. -/
def rememberTransaction (w : Wallet) (tx : Transaction) : WM Unit := do
  let s ← w.state
  let some k := historyIndex s tx.txid | return
  let updated := { s with history := s.history.modify k fun e =>
    { e with rawTransaction := some (tx.serialized false), fundingScripts := FundingSources.fundingScripts tx } }
  match updated.history[k]!.transaction with
  | .ok _ => pure ()
  | .error e => throw (if e == "invalidBundle" then .wallet (.invalidBundle "payment details do not match the transaction ID")
      else if e == "invalidTransactionAmounts" then .wallet .invalidTransactionAmounts else .named e)
  w.persist updated
  w.stateRef.set updated

/-! ### Keys and signing -/

def taprootKey (w : Wallet) (chain : AddressChain) (index : UInt32) (fingerprint : UInt32) (originPath : Array UInt32) :
    WM PSBT.TaprootKey := do
  let key ← WM.liftE (·.name) (do (← w.accountKey.child chain.rawValue.toUInt32).child index)
  return { internalKey := BIP86.xonlyPublicKey key, masterFingerprint := fingerprint,
           path := originPath ++ #[chain.rawValue.toUInt32, index] }

/-- The account private key, loaded for one signing operation: a root secret walked down the descriptor
origin, or an account secret at that origin (not derived again). Either way it must be private and its
public half this wallet's account key (`accountKeyMismatch`). -/
def accountPrivateKey (w : Wallet) : WM HDKey := do
  let o ← WM.wallet (origin w.descriptor)
  let resolved ← match ← WM.keys (w.keyStore.load w.id) with
    | .mnemonic words => WM.liftE (·.name) (do (← HDKey.ofSeed (BIP39.seed words)).derivedPath o.path)
    | .masterKey xprv => do WM.liftE (·.name) ((← WM.liftE (·.name) (HDKey.deserialize xprv)).derivedPath o.path)
    | .accountKey xprv fingerprint =>
      let key ← WM.liftE (·.name) (HDKey.deserialize xprv)
      unless fingerprint == o.fingerprint && key.depth.toNat == o.path.size && o.path.back? == some key.childIndex do
        throw (.wallet .accountKeyMismatch)
      pure key
  let neutered := resolved.neutered
  unless resolved.isPrivate && neutered.publicKey == w.accountKey.publicKey && neutered.chainCode == w.accountKey.chainCode &&
      neutered.depth == w.accountKey.depth && neutered.parentFingerprint == w.accountKey.parentFingerprint &&
      neutered.childIndex == w.accountKey.childIndex do
    throw (.wallet .accountKeyMismatch)
  return resolved

/-- The account private key, checked against this wallet's descriptor, for signing as a multisig signer
(`multisigSigningKey()`): the account xpub is the signer key the wallet shares, so one key signs whether
the wallet holds a seed, a master key or only its account key. -/
def multisigSigningKey (w : Wallet) : WM HDKey := w.accountPrivateKey

/-- BIP86 key-path secret below the account key already checked for this wallet. -/
def tweakedPrivateKey (_w : Wallet) (chain : AddressChain) (index : UInt32) (account : HDKey) : WM ByteArray := do
  let key ← WM.liftE (·.name) (do (← account.child chain.rawValue.toUInt32).child index)
  let some secret := key.privateKey | throw (.wallet (.invalidDescriptor "neutered key in signing path"))
  WM.liftE (·.name) (BIP86.tweakedPrivateKey secret)

/-- PSBTv2 metadata, a key-path signature per input, finalize, extract. -/
def sign (w : Wallet) (tx : Transaction) (selected : Array WalletUTXO) (changeIndex : Option UInt32)
    (changeOutputIndex : Option Nat) : WM (PSBT × Transaction) := do
  let o ← WM.wallet (origin w.descriptor)
  let inputInfo ← selected.mapM fun u => do
    return ({ spentOutput := u.spentOutput, key := some (← w.taprootKey u.chain u.index o.fingerprint o.path) } : PSBT.InputInfo)
  let mut outputInfo : Array PSBT.OutputInfo := #[]
  for i in [0:tx.outputs.size] do
    if let some ci := changeIndex then
      if changeOutputIndex == some i then
        let k ← w.taprootKey .change ci o.fingerprint o.path
        outputInfo := outputInfo.push { key := some k }
        continue
    outputInfo := outputInfo.push {}
  let mut psbt ← WM.liftE (·.name) (PSBT.create tx inputInfo outputInfo)
  let signingAccount ← w.accountPrivateKey
  for h : k in [0:selected.size] do
    let u := selected[k]
    let secret ← w.tweakedPrivateKey u.chain u.index signingAccount
    let aux ← WM.io w.random.auxRand
    psbt ← WM.liftE (·.name) (psbt.signKeyPath k secret aux)
  psbt ← WM.liftE (·.name) psbt.finalize
  let signed ← WM.liftE (·.name) psbt.extractedTransaction
  return (psbt, signed)

/-- The anti-fee-sniping locktime, drawing a second value only when the first takes the lookback branch. -/
def locktime (tip : UInt32) (draw : IO Float) : WM UInt32 := do
  let first ← WM.io draw
  if !(TransactionBuilder.draw first < 0.1) then return tip
  let second ← WM.io draw
  return TransactionBuilder.antiFeeSnipingLocktime tip first second

/-! ### Sending -/

/-- `SilentPayment(amount:address:network:)`: the code must carry the network's HRP (`sp` on mainnet,
`tsp` on the test networks). -/
def _root_.Winnow.Keys.SilentPayment.ofCode (amount : Int64) (code : String) (network : Tx.BitcoinNetwork) :
    Except SilentPaymentAddressError SilentPayment := do
  return { amount, address := ← SilentPaymentAddress.decode code (some (SilentPayment.hrp (network == .mainnet))) }

/-- The P2TR scripts of a send's silent payments, in order (`resolveSilentPayments`): BIP352 commits them to
the selected inputs, so this runs after coin selection, with the inputs' BIP86 key-path secrets (every coin
the wallet spends is one, the case where all inputs count). -/
def resolveSilentPayments (w : Wallet) (silentPayments : Array SilentPayment) (selected : Array WalletUTXO) :
    WM (Array Payment) := do
  if silentPayments.isEmpty then return #[]
  let account ← w.accountPrivateKey
  let inputs ← selected.toList.mapM fun u => do
    return ({ txid := u.txid, vout := u.vout, prevoutScriptPubKey := u.scriptPubKey,
              privateKey := ← w.tweakedPrivateKey u.chain u.index account } : SilentPaymentSending.Input)
  let scripts ← WM.liftE (·.name) (SilentPaymentSending.outputScripts inputs (silentPayments.toList.map (·.address)))
  return (silentPayments.zip scripts.toArray).map fun (p, script) => { amount := p.amount, scriptPubKey := script }

/-- Builds, signs and finalizes a send (mutation-free); change goes to the next unused internal address.
Silent payments are sized with a P2TR placeholder, and their scripts derived once coin selection has fixed
the inputs. -/
def buildSend (w : Wallet) (payments : Array Payment) (feeRateSatPerVByte : Float) (chainTip : UInt32)
    (draw : Option (IO Float) := none) (silentPayments : Array SilentPayment := #[]) : WM PreparedSend := do
  if payments.isEmpty && silentPayments.isEmpty then throw (.wallet .noPayments)
  let s ← w.state
  let changeIndex := s.nextChangeIndex
  let changeScript ← w.scriptPubKey .change changeIndex
  let sizing := payments ++ silentPayments.map fun p => { amount := p.amount, scriptPubKey := SilentPayment.sizingScriptPubKey }
  let selection ← WM.liftE (·.name) (CoinSelection.select (spendableUtxosOf s) sizing changeScript feeRateSatPerVByte)
  let resolved ← w.resolveSilentPayments silentPayments selection.selected
  let all := payments ++ resolved
  let change : Option Payment := selection.changeAmount.map fun a => { amount := a, scriptPubKey := changeScript }
  let lt ← locktime chainTip (draw.getD w.random.draw)
  let position ← match change with
    | some _ => some <$> WM.io (w.random.changePosition all.size)
    | none => pure none
  let tx ← WM.liftE (·.name) (TransactionBuilder.build (selection.selected.map (·.outpoint)) all change
    (changePosition := position.map Int.ofNat) (locktime := lt))
  let changeOutputIndex := change.bind fun c => tx.outputs.findIdx? fun o => o.scriptPubKey == c.scriptPubKey && o.value == c.amount
  let (psbt, signed) ← w.sign tx selection.selected (changeOutputIndex.map fun _ => changeIndex) changeOutputIndex
  WM.wallet (checkStandardSize signed)
  let codes ← silentPayments.mapM fun p => WM.liftE (·.name) p.address.encoded
  return { built := { psbt, transaction := signed, fee := selection.fee, changeAmount := selection.changeAmount },
           resolvedSilentPayments := resolved, silentPaymentAddresses := codes,
           selected := selection.selected, change, changeIndex,
           changeOutputIndex := changeOutputIndex.map (·.toUInt32), fee := selection.fee }

/-- The send's positive outputs by the watch map: change vouts, and every unwatched output as a recipient
(outputs to the wallet's own receive addresses are neither). -/
def classifyOutputs (w : Wallet) (s : WalletState) (tx : Transaction) : WM HistoryEntry.Outputs := do
  let map ← w.watchMap s
  return HistoryLedger.classifyOutputs tx fun script => map[script]?.map (·.1)

def tombstonePending (selected : Array WalletUTXO) (txid : ByteArray) (u : WalletUTXO) : WalletUTXO :=
  if selected.any (fun c => c.outpoint == u.outpoint) then { u with spent := some { spentBy := txid, height := none } } else u

/-- Commits a broadcast send: inputs tombstoned (no height), change pending at height 0. -/
def commit (w : Wallet) (prepared : PreparedSend) : WM Unit := do
  let signed := prepared.built.transaction
  let txid := signed.txid
  let s ← w.state
  let mut updated := { s with allUtxos := s.allUtxos.map (tombstonePending prepared.selected txid) }
  if let some change := prepared.change then
    let some vout := prepared.changeOutputIndex | throw (.wallet .changeOutputMissing)
    let some o := signed.outputs[vout.toNat]? | throw (.wallet .changeOutputMissing)
    unless o.scriptPubKey == change.scriptPubKey && o.value == change.amount do throw (.wallet .changeOutputMissing)
    updated := { updated with
      allUtxos := updated.allUtxos.push { txid := txid, vout := vout, amount := change.amount, scriptPubKey := change.scriptPubKey,
                                          chain := .change, index := prepared.changeIndex, height := 0 }
      nextChangeIndex := updated.nextChangeIndex + 1 }
  let outputs := (← w.classifyOutputs updated signed).annotateSilentPayments
    (prepared.resolvedSilentPayments.map fun p => (p.amount, p.scriptPubKey)) prepared.silentPaymentAddresses
  updated := { updated with
    history := updated.history.push {
      txid := txid, height := 0, received := (prepared.change.map (·.amount)).getD 0,
      spent := prepared.selected.foldl (fun a u => a + u.amount) 0, fee := some prepared.fee,
      rawTransaction := some (signed.serialized false), fundingScripts := FundingSources.fundingScripts signed,
      outputs := some outputs }
    pendingSends := updated.pendingSends.push {
      rawTransaction := signed.serialized true, selected := prepared.selected,
      changeIndex := if prepared.change.isNone then none else some prepared.changeIndex,
      changeOutputIndex := prepared.changeOutputIndex, fee := prepared.fee } }
  w.persist updated
  w.stateRef.set updated

/-! ### Fee bumping -/

structure FeeBumpCandidate where
  pending : PendingSend
  originalTxid : ByteArray
  transaction : Transaction
  fee : Int64
  change : Option Payment
  changeIndex : UInt32
  originalChangeOutputIndex : UInt32
  changeOutputIndex : Option UInt32
  currentFeeRate : Float
  replacementFeeRate : Float

def pendingFeeRate (w : Wallet) (txid : ByteArray) : WM Float := do
  let s ← w.state
  let some p := s.pendingSends.find? (pendingTxid · == some txid) | throw (.feeBump .transactionNotPending)
  let some tx := pendingTx p | throw (.feeBump .transactionNotPending)
  let vsize := TransactionBuilder.vsize tx
  if vsize == 0 then throw (.feeBump .transactionNotPending)
  return Float.ofInt p.fee.toInt / vsize.toFloat

def bumpablePendingSend (s : WalletState) (txid : ByteArray) (rate : Float) :
    Except FeeBumpError (PendingSend × Transaction × UInt32 × UInt32) := do
  let found := s.pendingSends.find? (pendingTxid · == some txid)
  let r : Option (PendingSend × Transaction × UInt32 × UInt32) := do
    let p ← found
    let original ← pendingTx p
    let ci ← p.changeIndex
    let coi ← p.changeOutputIndex
    if coi.toNat < original.outputs.size then some (p, original, ci, coi) else none
  let some (pending, original, changeIndex, coi) := r
    | throw (if found.isSome then .noChangeOutput else .transactionNotPending)
  unless s.utxos.any (fun u => u.txid == txid && u.vout == coi) do throw .changeAlreadySpent
  let oldVSize := TransactionBuilder.vsize original
  if oldVSize == 0 then throw .transactionNotPending
  let currentRate := Float.ofInt pending.fee.toInt / oldVSize.toFloat
  unless rate > currentRate do throw (.feeRateNotHigher currentRate rate)
  return (pending, original, changeIndex, coi)

/-- `Int64((x).rounded(.up))`. -/
def ceilI64 (x : Float) : Int64 := Int64.ofInt (x.ceil.toInt64.toInt)

def feeBumpCandidate (s : WalletState) (txid : ByteArray) (rate : Float) : WM FeeBumpCandidate := do
  unless rate.isFinite && rate > 0 && rate ≤ 10_000 do throw (.feeBump (.invalidFeeRate rate))
  let (pending, original, changeIndex, coi) ← match bumpablePendingSend s txid rate with
    | .ok r => pure r
    | .error e => throw (.feeBump e)
  let currentRate := Float.ofInt pending.fee.toInt / (TransactionBuilder.vsize original).toFloat
  let changeOutput := original.outputs[coi.toNat]!
  let mut payments : Array Payment := #[]
  for h : i in [0:original.outputs.size] do
    if i != coi.toNat then
      let o := original.outputs[i]
      payments := payments.push { amount := o.value, scriptPubKey := o.scriptPubKey }
  let inputTotal := pending.selected.foldl (fun a u => a + u.amount) (0 : Int64)
  let paymentTotal := payments.foldl (fun a p => a + p.amount) (0 : Int64)
  let maximumFee := inputTotal - paymentTotal
  let requiredFee (vsize : Int) : Int64 :=
    let requested := ceilI64 (Float.ofInt vsize * rate)
    let incremental := ceilI64 (Float.ofInt vsize * incrementalRelayFeeSatPerVByte)
    max requested (pending.fee + incremental)
  let paymentOutputs : Array Transaction.Output := payments.map fun p => { value := p.amount, scriptPubKey := p.scriptPubKey }
  let withChangeVSize := TransactionBuilder.signedVSize pending.selected.size (paymentOutputs.push changeOutput)
  let feeWithChange := requiredFee withChangeVSize
  let candidateChange := inputTotal - paymentTotal - feeWithChange
  let dust := CoinSelection.dustThreshold changeOutput.scriptPubKey
  let inputs := original.inputs.map (·.previousOutput)
  let (transaction, fee, change, replacementIndex) ←
    if candidateChange.toInt ≥ dust then do
      let change : Payment := { amount := candidateChange, scriptPubKey := changeOutput.scriptPubKey }
      let tx ← WM.liftE (·.name) (TransactionBuilder.build inputs payments (some change) (changePosition := some (Int.ofNat coi.toNat))
        (sequence := TransactionBuilder.defaultSequence) (locktime := original.locktime))
      pure (tx, feeWithChange, some change, some coi)
    else do
      let noChangeVSize := TransactionBuilder.signedVSize pending.selected.size paymentOutputs
      let minimum := requiredFee noChangeVSize
      unless maximumFee ≥ minimum do throw (.feeBump (.insufficientChange minimum maximumFee))
      let tx ← WM.liftE (·.name) (TransactionBuilder.build inputs payments none
        (sequence := TransactionBuilder.defaultSequence) (locktime := original.locktime))
      pure (tx, maximumFee, none, none)
  let replacementVSize := TransactionBuilder.signedVSize pending.selected.size transaction.outputs
  let actualRate := Float.ofInt fee.toInt / Float.ofInt replacementVSize
  unless fee > pending.fee && actualRate > currentRate do
    throw (.feeBump (.insufficientChange (pending.fee + 1) maximumFee))
  return { pending, originalTxid := txid, transaction, fee, change, changeIndex, originalChangeOutputIndex := coi,
           changeOutputIndex := replacementIndex, currentFeeRate := currentRate, replacementFeeRate := actualRate }

/-- The replacement's economics, without keys or mutation. -/
def previewFeeBump (w : Wallet) (txid : ByteArray) (rate : Float) : WM FeeBumpPreview := do
  let c ← feeBumpCandidate (← w.state) txid rate
  return { originalTxid := txid, currentFeeRateSatPerVByte := c.currentFeeRate, feeRateSatPerVByte := c.replacementFeeRate,
           fee := c.fee, changeAmount := c.change.map (·.amount), replacementTransaction := c.transaction }

/-- Rebuilds and signs the same-input replacement (mutation-free). -/
def buildFeeBump (w : Wallet) (txid : ByteArray) (rate : Float) : WM PreparedFeeBump := do
  let c ← feeBumpCandidate (← w.state) txid rate
  let (psbt, signed) ← w.sign c.transaction c.pending.selected (c.change.map fun _ => c.changeIndex)
    (c.changeOutputIndex.map (·.toNat))
  WM.wallet (checkStandardSize signed)
  return { originalTxid := txid, built := { psbt, transaction := signed, fee := c.fee, changeAmount := c.change.map (·.amount) },
           selected := c.pending.selected, originalChangeOutputIndex := c.originalChangeOutputIndex, change := c.change,
           changeIndex := c.changeIndex, changeOutputIndex := c.changeOutputIndex }

/-- Applies a broadcast replacement: the original row becomes replaced and its change is swapped. -/
def commitFeeBump (w : Wallet) (prepared : PreparedFeeBump) : WM Unit := do
  let s ← w.state
  let some pendingIndex := s.pendingSends.findIdx? (pendingTxid · == some prepared.originalTxid)
    | throw (.feeBump .transactionNotPending)
  let some historyIdx := s.history.findIdx? (fun e => e.txid == prepared.originalTxid && e.height == 0 && e.replacedBy.isNone)
    | throw (.feeBump .transactionNotPending)
  let signed := prepared.built.transaction
  let txid := signed.txid
  let mut updated := { s with allUtxos := s.allUtxos.filter fun u =>
    !(u.txid == prepared.originalTxid && u.vout == prepared.originalChangeOutputIndex) }
  if let some change := prepared.change then
    let some vout := prepared.changeOutputIndex | throw (.wallet .changeOutputMissing)
    let some o := signed.outputs[vout.toNat]? | throw (.wallet .changeOutputMissing)
    unless o.scriptPubKey == change.scriptPubKey && o.value == change.amount do throw (.wallet .changeOutputMissing)
    updated := { updated with allUtxos := updated.allUtxos.push {
      txid := txid, vout := vout, amount := change.amount,
      scriptPubKey := change.scriptPubKey, chain := .change, index := prepared.changeIndex, height := 0 } }
  updated := { updated with history := updated.history.modify historyIdx fun e => { e with replacedBy := some txid } }
  let mut outputs ← w.classifyOutputs updated signed
  if let some previous := updated.history[historyIdx]!.outputs then outputs := outputs.inheritSilentPayments previous
  updated := { updated with
    history := updated.history.push {
      txid := txid, height := 0, received := (prepared.change.map (·.amount)).getD 0,
      spent := prepared.selected.foldl (fun a u => a + u.amount) 0, fee := some prepared.built.fee,
      rawTransaction := some (signed.serialized false), fundingScripts := FundingSources.fundingScripts signed,
      outputs := some outputs }
    pendingSends := (updated.pendingSends.eraseIdx! pendingIndex).push {
      rawTransaction := signed.serialized true,
      selected := prepared.selected, changeIndex := if prepared.change.isNone then none else some prepared.changeIndex,
      changeOutputIndex := prepared.changeOutputIndex, fee := prepared.built.fee } }
  w.persist updated
  w.stateRef.set updated

/-! ### Export -/

/-- Live wallet → import bundle (watch-only unless `includeMnemonic`), payments no block has taken
included: unconfirmed coins among the UTXOs, and each pending send with the coins it reserves. -/
def exportBundle (w : Wallet) (includeMnemonic : Bool := false) : WM ImportBundle := do
  let s ← w.state
  let lastKnownHeight := if s.nextScanHeight == 0 then 0 else s.nextScanHeight - 1
  let mnemonic ← if includeMnemonic then do
      match ← WM.io (w.keyStore.load w.id).run with
      | .ok (.mnemonic words) => pure (some words)
      | .ok (.masterKey _) | .ok (.accountKey ..) => throw (.wallet .mnemonicUnavailable)
      | .error (.notFound _) => throw (.wallet .mnemonicUnavailable)
      | .error e => throw (.named e.name)
    else pure none
  return ImportBundle.«export» w.descriptor.serialized (networkName w.network) lastKnownHeight s.utxos s.history
    s.nextReceiveIndex s.nextChangeIndex mnemonic s.scannedThroughHash s.pendingSends

/-! ### Rollback -/

/-- The coin rows a fork takes away (reserved rows stay, re-heighted to 0). -/
def rewindCoins (forkHeight : UInt32) (coins : Array WalletUTXO) : Array WalletUTXO :=
  let kept := coins.filter fun c =>
    let reserved := c.spent.isSome && (c.spent.bind (·.height)).isNone
    !(c.height > forkHeight && !reserved)
  kept.map fun c => if c.height > forkHeight then { c with height := 0 } else c

/-- A disconnected spender is still live in mempools (`HistoryLedger.rewind` re-pended its entry): its input
reservations are retained before the coins rewind. Spent by something that fell with the fork entirely:
restored. -/
def keepReservations (repended : Array ByteArray) (forkHeight : UInt32) (coins : Array WalletUTXO) : Array WalletUTXO :=
  coins.map fun u => match u.spent with
    | some m => match m.height with
      | some h => if h > forkHeight then
          { u with spent := if repended.contains m.spentBy then some { spentBy := m.spentBy, height := none } else none }
        else u
      | none => u
    | none => u

/-- Rewinds every chain-derived fact to `forkHeight` (idempotent; address indices untouched). -/
def rollBack (w : Wallet) (forkHeight : UInt32) : WM Unit := do
  let s ← w.state
  let (history, repended) := HistoryLedger.rewind s.history forkHeight
  let mut candidate := { s with
    allUtxos := rewindCoins forkHeight (keepReservations repended forkHeight s.allUtxos)
    history
    nextScanHeight := min s.nextScanHeight (if forkHeight == 0xFFFF_FFFF then forkHeight else forkHeight + 1) }
  -- A frontier that moved back names a block this rewind just doubted.
  if candidate.nextScanHeight != s.nextScanHeight then candidate := { candidate with scannedThroughHash := none }
  if candidate == s then return
  w.persist candidate
  w.stateRef.set candidate

/-! ### Import -/

def importedKeyMaterial (bundle : ImportBundle) (network : BitcoinNetwork) (keyStore : KeyStore IO) :
    WM (Descriptor × HDKey) := do
  if let some mnemonic := bundle.mnemonic then
    WM.liftE (·.name) (BIP39.validate mnemonic)
    let master ← WM.liftE (·.name) (HDKey.ofSeed (BIP39.seed mnemonic))
    let ct := coinType network
    let account ← WM.liftE (·.name) (BIP86.accountKey master ct 0)
    let o : Descriptor.KeyOrigin := { fingerprint := master.fingerprint, path := #[86, ct, 0].map (· + HDKey.hardenedOffset) }
    let derived := makeDescriptor account o network
    if let some text := bundle.descriptor then
      let parsed ← WM.liftE (·.name) (Descriptor.parse text)
      if parsed.serialized != derived.serialized then throw (.wallet .descriptorMismatch)
    let walletID := hex8 master.fingerprint
    match ← WM.io (keyStore.store (.mnemonic mnemonic) walletID).run with
    | .ok () => pure ()
    | .error (.alreadyExists _) =>
      let existing ← WM.keys (keyStore.load walletID)
      unless existing == .mnemonic mnemonic do throw (.named "alreadyExists")
    | .error e => throw (.named e.name)
    return (derived, account.neutered)
  let some text := bundle.descriptor | throw (.wallet (.invalidBundle "no usable descriptor"))
  let parsed ← WM.liftE (·.name) (Descriptor.parse text)
  discard <| WM.wallet (origin parsed)
  let .tr key := parsed.expression | throw (.wallet (.invalidDescriptor text))
  let .extended account _ := key.base | throw (.wallet (.invalidDescriptor text))
  return (parsed, account.neutered)

/-- A coin's script is the descriptor's at its chain and index. -/
def requireOwned (descriptor : Descriptor) (network : BitcoinNetwork) (u : WalletUTXO) : WM Unit := do
  let outs ← WM.liftE (·.name) (descriptor.derived u.index network)
  let some o := outs[u.chain.rawValue]? | throw (.named "indexOutOfRange")
  unless o.scriptPubKey == u.scriptPubKey do
    throw (.wallet (.invalidBundle s!"utxo {displayHex u.txid}:{u.vout} scriptPubKey does not match the descriptor"))

def validatedClaimedUTXOs (bundle : ImportBundle) (descriptor : Descriptor) (network : BitcoinNetwork) :
    WM (Array WalletUTXO) := do
  let utxos ← WM.wallet bundle.claimedUTXOs
  for u in utxos do requireOwned descriptor network u
  return utxos

/-- The bundle's pending sends, checked: each transaction decodes, spends exactly its selected coins (the
wallet's own, none also claimed unspent or spent by another pending send), and names a change output it
has. The coins come back reserved by the payment, as `send` left them. -/
def validatedPendingSends (bundle : ImportBundle) (descriptor : Descriptor) (network : BitcoinNetwork)
    (claimed : Array WalletUTXO) : WM (Array PendingSend × Array WalletUTXO) := do
  let invalid (reason : String) : WM Unit := throw (.wallet (.invalidBundle s!"pending payment: {reason}"))
  let mut seen : Std.HashSet (ByteArray × UInt32) := claimed.foldl (fun s u => s.insert (u.txid, u.vout)) {}
  let mut reserved : Array WalletUTXO := #[]
  for p in bundle.pendingSends do
    let .ok tx := Transaction.decode p.rawTransaction | throw (.wallet (.invalidBundle "pending payment: the transaction does not decode"))
    unless WalletState.inMoney p.fee do invalid "invalid fee"
    unless p.selected.size == tx.inputs.size && tx.inputs.all (fun i => p.selected.any (·.outpoint == i.previousOutput)) do
      invalid "its coins are not its inputs"
    if let some k := p.changeOutputIndex then unless k.toNat < tx.outputs.size do invalid "no such change output"
    for c in p.selected do
      unless c.amount > 0 && c.amount ≤ bitcoinAmountMaximum && c.txid.size == 32 do invalid "invalid coin"
      requireOwned descriptor network c
      if seen.contains (c.txid, c.vout) then invalid "a coin is spent twice"
      seen := seen.insert (c.txid, c.vout)
      reserved := reserved.push { c with spent := some { spentBy := tx.txid, height := none } }
  return (bundle.pendingSends, reserved)

/-- A claimed block hash in internal byte order, or `none` when the bundle names none; a pending entry
has no block to name. -/
def claimedBlockHash (hex? : Option String) (confirmed : Bool) : Except WalletError (Option ByteArray) := do
  let some text := hex? | return none
  let bad : WalletError := .invalidBundle s!"bad block hash {ImportBundle.excerpt text}"
  unless confirmed do throw bad
  let some hash := Wire.dataOfHex? text | throw bad
  unless hash.size == 32 do throw bad
  return some (ByteArray.reverse hash)

def validatedHistory (bundle : ImportBundle) : WM (Array HistoryEntry) :=
  bundle.transactions.mapM fun known => do
    let some txid := Wire.dataOfHex? known.txid | throw (.wallet (.invalidBundle s!"bad txid {known.txid}"))
    unless txid.size == 32 do throw (.wallet (.invalidBundle s!"bad txid {known.txid}"))
    let replacedBy ← match known.replacedBy with
      | some r => match Wire.dataOfHex? r with
        | some b => if b.size == 32 then pure (some (ByteArray.reverse b)) else throw (.wallet (.invalidBundle s!"bad replacement txid {r}"))
        | none => throw (.wallet (.invalidBundle s!"bad replacement txid {r}"))
      | none => pure none
    unless WalletState.inMoney known.received && WalletState.inMoney known.spent && (known.fee.map WalletState.inMoney).getD true do
      throw (.wallet (.invalidBundle "transaction history has invalid amounts"))
    let blockHash ← WM.wallet (claimedBlockHash known.blockHash (known.height > 0))
    let entry : HistoryEntry := {
      txid := ByteArray.reverse txid, height := known.height, received := known.received,
      spent := known.spent, fee := known.fee, replacedBy := replacedBy, rawTransaction := known.rawTransaction,
      blockHash, outputs := known.outputs }
    match entry.checkedTransaction with
    | .ok _ => pure entry
    | .error (.inl e) => throw (.wallet e)
    | .error (.inr e) => throw (.named e)

/-- `max(index) + 1` over the coins on `chain`, or 0. -/
def nextIndexAfter (utxos : Array WalletUTXO) (chain : AddressChain) : UInt32 :=
  match (utxos.filter (·.chain == chain)).map (·.index) with
  | #[] => 0
  | xs => xs.foldl max 0 + 1

/-- Seeds a wallet from an import bundle; scanning resumes after its `lastKnownHeight`. -/
def importing (bundle : ImportBundle) (keyStore : KeyStore IO) (storagePath : Option System.FilePath := none)
    (random : Randomness := .system) : WM Wallet := do
  unless ImportBundle.supportedVersions bundle.version do
    throw (.wallet (.invalidBundle s!"unsupported version {bundle.version}"))
  let some network := BitcoinNetwork.ofString? bundle.network
    | throw (.wallet (.invalidBundle s!"unknown network {ImportBundle.excerpt bundle.network}"))
  if bundle.descriptor.isNone && bundle.mnemonic.isNone then
    throw (.wallet (.invalidBundle "need a descriptor or a mnemonic"))
  let (descriptor, accountKey) ← importedKeyMaterial bundle network keyStore
  let utxos ← validatedClaimedUTXOs bundle descriptor network
  let history ← validatedHistory bundle
  let (pendingSends, reserved) ← validatedPendingSends bundle descriptor network utxos
  let maxIndex (chain : AddressChain) : UInt32 := nextIndexAfter (utxos ++ reserved) chain
  let receive := max (bundle.nextReceiveIndex.getD 0) (maxIndex .receive)
  let change := max (bundle.nextChangeIndex.getD 0) (maxIndex .change)
  let maximum := HDKey.hardenedOffset - gapLimit
  unless receive ≤ maximum && change ≤ maximum do
    throw (.wallet (.invalidBundle "address cursors leave no room for the gap-limit window"))
  unless bundle.lastKnownHeight < 0xFFFF_FFFF do
    throw (.wallet (.invalidBundle s!"last known height {bundle.lastKnownHeight} is out of range"))
  let scannedThroughHash ← WM.wallet (claimedBlockHash bundle.lastKnownBlockHash true)
  let state : WalletState := {
    descriptor := descriptor.serialized, network := networkName network,
    creationHeight := bundle.lastKnownHeight,
    nextReceiveIndex := receive, nextChangeIndex := change,
    nextScanHeight := bundle.lastKnownHeight + 1, scannedThroughHash, allUtxos := utxos ++ reserved, history,
    pendingSends }
  let w ← make network descriptor accountKey keyStore storagePath random state
  persistState storagePath state
  return w

/-- Verifies an imported bundle by scanning forward and comparing the outcome with its claims. -/
def verifyImport (w : Wallet) (bundle : ImportBundle) (source : ScanSource) (additionalScripts : Array ByteArray := #[])
    (onMatch : Net.BlockMatch → WM Unit := fun _ => pure ()) : WM ImportReport := do
  let fromHeight ← WM.io source.nextScanHeight
  let effects ← WM.io (IO.mkRef (#[] : Array MatchEffect))
  source.sync ((← w.watchScripts) ++ additionalScripts) fun m => do
    let e ← w.apply m
    WM.io (effects.modify (·.push e))
    onMatch m
  let toHeight ← WM.io source.lastScannedHeight
  WM.wallet (ImportReport.make bundle (← WM.io effects.get) (← w.utxos) fromHeight toHeight)

end Wallet

/-- A `ScanSource` that replays given matches (tests, and the pure core of a real scan). -/
def ScanSource.scripted (fromHeight : UInt32) (blocks : Array Net.BlockMatch) (lastScanned : Option UInt32) : ScanSource where
  nextScanHeight := pure fromHeight
  lastScannedHeight := pure lastScanned
  sync _ f := blocks.forM f

end Winnow
