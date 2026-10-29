import Std.Data.HashMap
import Std.Sync.Mutex
import Std.Data.HashSet
import WinnowApp.Real.RecordsStores
import Winnow.Ledger.Multisig

/-! # The multisig account store (port of `Sources/WinnowApp/MultisigStore.swift`, upstream d2ca878)

App-side multisig bookkeeping: the persisted `MultisigAccountRecord`s plus the coin and history tracking
`Wallet` performs for the wallet itself, fed by the same combined filter scan (an account is just more
watched scripts), and the one spend per account this phone is collecting signatures for (its draft) or
has broadcast (in flight). One sealed JSON file per wallet, `multisig.json`, cleared with the other
per-wallet files. Damage is reported, the file left untouched and every mutation refused until it reads
again; the wallet itself carries on.

Fixed upstream bug (PORT.md, "Fixed upstream bugs" 3): `apply` reports the person a draft paid when the
draft's own transaction confirms, whoever broadcast it, so the app advances that person's address
index; upstream advanced it only when this phone broadcast the draft.

As `RecordsStores.lean` does for the people store, the Swift actor becomes an immutable value: every
mutation returns the next store (or fails and the caller keeps the old one), so "apply to a copy,
validate, persist, adopt only when every step succeeded" is "return the new store". `MultisigHost` keeps
the current value behind one mutex.

Differences of form:
* The file is the sealed `[MultisigAccountRecord]` array written by `SwiftJSON.write` (sorted keys,
  escaped slashes); Swift's `JSONEncoder()` writes the same values in its own key order. Either reads.
* The owner-map cache is part of the value (the next store carries it). -/

namespace WinnowApp.RecordsReal
open Winnow SwiftJSON
open Tx (BitcoinNetwork)

/-- `script → (choice, index)` for every address a record watches. -/
abbrev OwnerMap := Std.HashMap ByteArray (Nat × UInt32)

/-- A record's watched scripts for one descriptor, indices `0 ..< count` (both choices, index-major) and
the owner map over them. Deriving one index costs a BIP32 step per key and a Taproot tweak, so the cache
grows with the frontier instead of being rebuilt. -/
structure OwnerCache where
  id : String
  descriptor : String
  count : UInt32
  scripts : Array ByteArray
  owner : OwnerMap
  deriving Inhabited

/-- A failure of a `MultisigAccount` call, as the screens describe it. -/
def multisigFailure (network : BitcoinNetwork) : MultisigFailure → RecordsError
  | .account e => .named e.name e.description
  | .named n => namedError n network

def liftAccount {α} (network : BitcoinNetwork) (r : MAM α) : RM α := RM.lift (multisigFailure network) r

/-- `MultisigStore`. -/
structure MultisigStore where
  records : Array MultisigAccountRecord := #[]
  path : Option System.FilePath := none
  network : BitcoinNetwork := .signet
  isDamaged : Bool := false
  /-- Each record's owner map, kept until its descriptor or watch count changes: (id, descriptor,
  watch count, map). -/
  ownerMaps : Array OwnerCache := #[]
  deriving Inhabited

namespace MultisigStore

def maximumAccounts : Nat := 100
/-- A record watches at most this many indices plus `Wallet.gapLimit`. -/
def maximumNextIndex : UInt32 := 10_000 - 2
def maximumFileBytes : Nat := 16 * 1_024 * 1_024
def maximumMoney : Int := 2_100_000_000_000_000
/-- Blocks after which a confirmed spend's bytes are no longer kept for announcing it again. -/
def inFlightDepth : UInt32 := 6
def storeName : String := "multisig"
def fileName : String := "multisig.json"

def damagedStorageMessage : String :=
  "Winnow found multisig account data but could not safely read it. The file and protected keys were left untouched. Retry; if this continues, restore from a known-good wallet bundle or ask for help before changing anything."

def unverifiedStorageMessage : String :=
  "Winnow found multisig account data it could not verify: the file was not written by Winnow on this device, or its protected key is gone. The file and protected keys were left untouched. Restore your multisig accounts from a known-good wallet bundle, or ask for help before changing anything."

def invalid {α} (reason : String) : RM α := throw (.multisig (.invalidState reason))

def storeSeal (keys : StoreKeyVault) : StoreSeal := { store := storeName, keys }

/-- Indices `0 ..< max(used receive, used change) + Wallet.gapLimit` on both chains. -/
def watchCount (r : MultisigAccountRecord) : UInt32 := max r.nextReceiveIndex r.nextChangeIndex + Wallet.gapLimit

/-! ## Validation -/

/-- A usable name, a canonical descriptor whose checksum is the record's id, a supported account on this
network, and indices in range. -/
def validatedShape (r : MultisigAccountRecord) (network : BitcoinNetwork) : RM MultisigAccount := do
  unless DisplayName.normalized r.name == some r.name && !r.name.isEmpty do invalid "an account has no usable name"
  let account ← liftAccount network (MultisigAccount.parse r.descriptor network)
  unless account.descriptor.serialized == r.descriptor && account.id == r.id do
    invalid "account descriptor identifier does not match"
  unless (r.checkLedgerRegistration account).toOption.isSome do
    invalid "an account's Ledger registration does not match it"
  unless r.nextReceiveIndex ≤ maximumNextIndex && r.nextChangeIndex ≤ maximumNextIndex do
    invalid "account address index is out of range"
  return account

/-- One coin re-derived below its frontier, never repeated across the store, with the live total kept
inside Bitcoin's range. -/
def validateCoin (u : WalletUTXO) (r : MultisigAccountRecord) (account : MultisigAccount) (network : BitcoinNetwork)
    (cache : Option OwnerCache) (outpoints : Std.HashSet String) (total : Int) : RM (Std.HashSet String × Int) := do
  unless u.txid.size == 32 && u.amount > 0 && u.amount.toInt ≤ maximumMoney &&
      (u.spent.all (·.spentBy.size == 32)) do
    invalid "account coin metadata is invalid"
  let frontier := if u.chain == .receive then r.nextReceiveIndex else r.nextChangeIndex
  unless u.index < frontier do invalid "an account coin does not belong to its descriptor"
  -- the derived script at the coin's coordinates, read from the owner map when it covers them
  let derive : RM Bool := do
    let script ← liftAccount network (account.scriptPubKey u.index u.chain.rawValue)
    pure (script == u.scriptPubKey)
  let belongs ← match cache with
    | some c => if u.index < c.count then pure (c.owner[u.scriptPubKey]? == some (u.chain.rawValue, u.index)) else derive
    | none => derive
  unless belongs do invalid "an account coin does not belong to its descriptor"
  let key := outpointKey u.txid u.vout
  if outpoints.contains key then invalid "duplicate account coin"
  let outpoints := outpoints.insert key
  -- Spent rows can return after a reorg, so their ownership is checked too; only live coins count.
  if u.isSpent then return (outpoints, total)
  let sum := total + u.amount.toInt
  unless sum ≤ maximumMoney do invalid "account balance is outside Bitcoin's monetary range"
  return (outpoints, sum)

/-- `validateHistory(of:)`: each entry one transaction, listed once, with amounts in range and bytes that
match its txid. -/
def validateHistory (r : MultisigAccountRecord) : RM Unit := do
  unless r.history.size ≤ ImportBundle.maximumEntries do invalid "too many account transactions"
  let mut txids : Std.HashSet ByteArray := {}
  let inRange (v : Int64) : Bool := 0 ≤ v.toInt && v.toInt ≤ maximumMoney
  for e in r.history do
    let bytesOK := match e.transaction with
      | .ok (some _) => true
      | .ok none => e.rawTransaction.isNone
      | .error _ => false
    unless e.txid.size == 32 && !txids.contains e.txid && inRange e.received && inRange e.spent &&
        (e.fee.all inRange) && bytesOK do
      invalid "an account transaction record is invalid"
    txids := txids.insert e.txid

/-- `validateSpends(of:)`: a draft that parses and spends only the account's live coins, and in-flight
bytes that are the spends they name, each in the history. -/
def validateSpends (r : MultisigAccountRecord) : RM Unit := do
  if let some d := r.draft then
    let live := r.utxos.map (·.outpoint)
    let ok := match d.inputs with
      | .ok inputs => !inputs.isEmpty && inputs.all live.contains
      | .error _ => false
    unless ok do invalid "an account's draft does not spend its live coins"
  unless r.inFlight.size ≤ maximumAccounts do invalid "too many in-flight account spends"
  for f in r.inFlight do
    unless f.transaction.toOption.isSome && r.history.any (·.txid == f.txid) do
      invalid "an in-flight account spend is not in its history"

/-- Every record re-derived (`MultisigStore.validate`); `caches` are owner maps already derived for these
descriptors. -/
def validate (records : Array MultisigAccountRecord) (network : BitcoinNetwork) (caches : Array OwnerCache := #[]) :
    RM Unit := do
  unless records.size ≤ maximumAccounts do throw (.multisig .tooMany)
  let mut ids : Std.HashSet String := {}
  let mut outpoints : Std.HashSet String := {}
  let mut total : Int := 0
  for r in records do
    if ids.contains r.id then invalid "duplicate account identifier"
    ids := ids.insert r.id
    let account ← validatedShape r network
    let cache := caches.find? fun c => c.id == r.id && c.descriptor == r.descriptor
    for u in r.allUtxos do
      (outpoints, total) ← validateCoin u r account network cache outpoints total
    validateHistory r
    validateSpends r

/-! ## Persistence -/

def encode (records : Array MultisigAccountRecord) : ByteArray :=
  (write (.arr (records.map MultisigAccountRecord.toJV))).toUTF8

def decode (payload : ByteArray) : RM (Array MultisigAccountRecord) := do
  let some text := String.fromUTF8? payload | throw (.named "dataCorrupted" "The multisig account file is not valid JSON.")
  RM.lift (fun e => .named e "The multisig account file could not be decoded.") (decodeText text (asArray MultisigAccountRecord.ofJV))

/-- `mutate`: persist the candidate records, then adopt them (the old store stays when the write fails). -/
def mutate (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (candidate : Array MultisigAccountRecord) :
    RM MultisigStore := do
  if let some p := s.path then (storeSeal keys).write (encode candidate) s.network p writeData
  return { s with records := candidate }

/-- `configure(storageURL:network:)`: loads an existing file. An unsealed one was put there by something
else (no Winnow wrote this file before sealing existed), so it is refused. -/
def configure (keys : StoreKeyVault) (path : Option System.FilePath) (network : BitcoinNetwork) :
    IO (MultisigStore × OpenResult) := do
  let empty : MultisigStore := { path, network }
  let some p := path | return (empty, .missing)
  -- a store the Swift app left is set aside and starts empty; if that fails, it reads as damage below
  discard <| ((storeSeal keys).setAsideSwiftEra network p).run
  unless ← fileExists p do return (empty, .missing)
  let attempt : RM (Array MultisigAccountRecord) := do
    let data ← boundedRead p maximumFileBytes (.multisig (.invalidState "account file too large"))
    let (payload, predates) ← (storeSeal keys).read data network
    if predates then throw (.seal .unsealed)
    let decoded ← decode payload
    validate decoded network
    return decoded
  match ← attempt.run with
  | .ok records => return ({ empty with records }, .loaded)
  | .error e =>
    return ({ empty with isDamaged := true },
            .damaged (if isSealFailure e then unverifiedStorageMessage else damagedStorageMessage))

def record? (s : MultisigStore) (id : String) : Option MultisigAccountRecord := s.records.find? (·.id == id)

def requireReadable (s : MultisigStore) : RM Unit := do
  if s.isDamaged then throw (.multisig .damaged)

/-- The records for a wallet bundle, pending state included: coins no block has taken, spends in flight
with the bytes to announce them again, and the draft being signed, so a restored phone picks up where
this one was instead of forgetting a payment that was never confirmed. -/
def backupRecords (s : MultisigStore) : RM (Array MultisigAccountRecord) := do
  s.requireReadable
  return s.records

/-- Replaces the records with a restored bundle's. -/
def restore (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (restored : Array MultisigAccountRecord) :
    RM MultisigStore := do
  s.requireReadable
  validate restored s.network
  s.mutate keys writeData restored

/-- `add(name:account:createdAtHeight:)`. -/
def add (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (name : String) (account : MultisigAccount)
    (createdAtHeight : UInt32) : RM (MultisigStore × MultisigAccountRecord) := do
  s.requireReadable
  unless DisplayName.normalized name == some name && !name.isEmpty do
    invalid "an account needs a short, single-line name"
  unless account.network == s.network do invalid "the account's network does not match the open wallet"
  if s.records.any (·.id == account.id) then throw (.multisig .duplicate)
  unless s.records.size < maximumAccounts do throw (.multisig .tooMany)
  let record : MultisigAccountRecord :=
    { id := account.id, name, descriptor := account.descriptor.serialized, createdAtHeight }
  return (← s.mutate keys writeData (s.records.push record), record)

def remove (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) : RM MultisigStore := do
  s.requireReadable
  let next ← s.mutate keys writeData (s.records.filter (·.id != id))
  return { next with ownerMaps := next.ownerMaps.filter (·.id != id) }

/-- The record's owner cache at its watch count: from the cache while the descriptor is the one it was
built for (extended when the frontier moved on); the store with the cache updated. -/
def ownerCache (s : MultisigStore) (r : MultisigAccountRecord) : RM (OwnerCache × MultisigStore) := do
  let count := watchCount r
  let start : OwnerCache := match s.ownerMaps.find? fun c => c.id == r.id && c.descriptor == r.descriptor with
    | some c => c
    | none => { id := r.id, descriptor := r.descriptor, count := 0, scripts := #[], owner := {} }
  if start.count ≥ count then return (start, s)
  let account ← liftAccount s.network (MultisigAccount.parse r.descriptor s.network)
  let mut c := start
  for index in [start.count.toNat:count.toNat] do
    let outputs ← liftAccount s.network (MultisigAccount.lift (·.name) (account.descriptor.derived index.toUInt32 s.network))
    for h : choice in [0:outputs.size] do
      if choice < 2 then
        c := { c with scripts := c.scripts.push outputs[choice].scriptPubKey,
                      owner := c.owner.insert outputs[choice].scriptPubKey (choice, index.toUInt32) }
  c := { c with count }
  return (c, { s with ownerMaps := (s.ownerMaps.filter (·.id != r.id)).push c })

/-- The cache entries of `records` (deriving what is missing). -/
def ownerCaches (s : MultisigStore) (records : Array MultisigAccountRecord) : RM (Array OwnerCache × MultisigStore) := do
  let mut store := s
  let mut out := #[]
  for r in records do
    let (c, next) ← store.ownerCache r
    store := next
    out := out.push c
  return (out, store)

/-- Receive and change scripts of every account below its watch count, for the combined scan. -/
def watchScripts (s : MultisigStore) (network : BitcoinNetwork) : RM (Array ByteArray × MultisigStore) := do
  unless network == s.network do invalid "the account network does not match the open wallet"
  let (caches, store) ← s.ownerCaches s.records
  return (caches.foldl (fun acc c => acc ++ c.scripts.extract 0 (2 * (watchCountOf c s.records).toNat)) #[], store)
where
  watchCountOf (c : OwnerCache) (records : Array MultisigAccountRecord) : UInt32 :=
    ((records.find? (·.id == c.id)).map watchCount).getD c.count

def isPending (u : WalletUTXO) : Bool := u.spent.any (·.height.isNone)

/-- Undoes in-flight spends a confirmed conflict beat (as `Wallet.reconcilePendingConflict`): their pending
outputs go, the inputs the winner did not take are released, and an in-flight spend of one of those
outputs loses with them. Every spend undone. -/
def dropLosingSpends (losers : Array ByteArray) (r : MultisigAccountRecord) : MultisigAccountRecord × Array ByteArray := Id.run do
  let mut queue := losers.toList
  let mut dropped : Array ByteArray := #[]
  let mut coins := r.allUtxos
  repeat
    match queue with
    | [] => break
    | loser :: rest =>
      queue := rest
      if dropped.contains loser then continue
      dropped := dropped.push loser
      let neverExisted := fun (u : WalletUTXO) => u.txid == loser && u.height == 0
      queue := queue ++ (coins.filter neverExisted).toList.filterMap fun u =>
        u.spent.bind fun m => if m.height.isNone then some m.spentBy else none
      coins := coins.filter (!neverExisted ·)
      let reservation : SpentMarker := { spentBy := loser, height := none }
      coins := coins.map fun u => if u.spent == some reservation then { u with spent := none } else u
  return ({ r with allUtxos := coins }, dropped)

/-- `retire(_:replacedBy:in:)`: a spend that lost keeps its entry, marked replaced by the winner, and its
bytes are no longer worth announcing. -/
def retire (dropped : Array ByteArray) (winner : ByteArray) (r : MultisigAccountRecord) : MultisigAccountRecord :=
  { r with history := r.history.map (fun e => if dropped.contains e.txid then { e with replacedBy := some winner } else e),
           inFlight := r.inFlight.filter (!dropped.contains ·.txid) }

/-- What one transaction's inputs did to a record: whether it changed, what left the account, and whether
every input was its coin (which makes the fee exact). -/
structure SpendEffect where
  changed : Bool := false
  spent : Int64 := 0
  allInputsOurs : Bool := false
  dropped : Array ByteArray := #[]

/-- Tombstones the record's coins `tx` spends, and learns the height of tombstones written while the spend
was only in flight; a tombstone naming another transaction lost the race and is undone (and retired). -/
def applySpends (tx : Transaction) (txid : ByteArray) (height : UInt32) (r : MultisigAccountRecord) :
    MultisigAccountRecord × SpendEffect := Id.run do
  let mut coins := r.allUtxos
  let mut changed := false
  let mut spent : Int64 := 0
  let mut allInputsOurs := !tx.inputs.isEmpty
  let mut losers : Array ByteArray := #[]
  for input in tx.inputs do
    let outpoint := input.previousOutput
    if let some live := coins.findIdx? (fun u => !u.isSpent && u.outpoint == outpoint) then
      -- Marked, not removed, so a reorg can put it back.
      spent := spent + coins[live]!.amount
      coins := coins.modify live fun u => { u with spent := some { spentBy := txid, height := some height } }
      changed := true
    else if let some pending := coins.findIdx? (fun u => isPending u && u.outpoint == outpoint) then
      if let some m := coins[pending]!.spent then
        if m.spentBy != txid then losers := losers.push m.spentBy
      spent := spent + coins[pending]!.amount
      coins := coins.modify pending fun u => { u with spent := some { spentBy := txid, height := some height } }
      changed := true
    else allInputsOurs := false
  -- After every input, so a coin both spends took stays the winner's.
  let (r', dropped) := dropLosingSpends losers { r with allUtxos := coins }
  return (retire dropped txid r', { changed, spent, allInputsOurs, dropped })

/-- Admits every watched output as a coin (or re-heights one already known) and advances the frontiers. -/
def applyOutputs (tx : Transaction) (txid : ByteArray) (owner : OwnerMap) (count : UInt32) (height : UInt32)
    (isCoinbase : Bool) (r : MultisigAccountRecord) : RM (MultisigAccountRecord × Bool × Int64) := do
  let mut r := r
  let mut changed := false
  let mut received : Int64 := 0
  for h : vout in [0:tx.outputs.size] do
    let output := tx.outputs[vout]
    -- Zero-value outputs are not coins: admitting one fails `validate`, and the scan would retry forever.
    unless output.value > 0 do continue
    let some (choice, index) := owner[output.scriptPubKey]? | continue
    -- the cache can reach past this record's window (after a restore lowered its frontiers)
    unless index < count do continue
    unless vout < 2 ^ 32 do invalid "transaction output index is out of range"
    match r.allUtxos.findIdx? (fun u => u.txid == txid && u.vout == vout.toUInt32) with
    | some existing =>
      -- A re-applied block, our own pending change confirming, or a coin a rollback kept at height 0 for a
      -- spend in flight. Only the last is a receive to count: its entry fell with its block.
      let refound := r.allUtxos[existing]!.height == 0 && !r.history.any (·.txid == txid)
      r := { r with allUtxos := r.allUtxos.modify existing fun u => { u with height } }
      if refound then received := received + output.value
    | none =>
      let coin : WalletUTXO :=
        { txid, vout := vout.toUInt32, amount := output.value, scriptPubKey := output.scriptPubKey,
          chain := if choice == 1 then .change else .receive, index, height, isCoinbase }
      r := { r with allUtxos := r.allUtxos.push coin }
      received := received + output.value
    changed := true
    if choice == AddressChain.receive.rawValue && index ≥ r.nextReceiveIndex then r := { r with nextReceiveIndex := index + 1 }
    if choice == AddressChain.change.rawValue && index ≥ r.nextChangeIndex then r := { r with nextChangeIndex := index + 1 }
  return (r, changed, received)

/-- `pruneDraft(of:)`: a draft whose input is no longer a live coin of the account can never be broadcast
(this phone broadcast it, a co-signer's spend confirmed, or a reorg took a coin). The record, and the
draft dropped. -/
def pruneDraft (r : MultisigAccountRecord) : MultisigAccountRecord × Option MultisigSpendDraft :=
  match r.draft with
  | none => (r, none)
  | some d =>
    let live := r.utxos.map (·.outpoint)
    match d.inputs with
    | .ok inputs => if inputs.all live.contains then (r, none) else ({ r with draft := none }, some d)
    | .error _ => ({ r with draft := none }, some d)

/-- `settle(_:at:)`: after a block, a draft whose input is gone is dropped, and the bytes of spends buried
`inFlightDepth` blocks deep are no longer kept. -/
def settle (r : MultisigAccountRecord) (height : UInt32) : MultisigAccountRecord × Bool × Option MultisigSpendDraft :=
  let (r, dropped) := pruneDraft r
  let before := r.inFlight.size
  let inFlight := r.inFlight.filter fun f =>
    match r.history.find? (·.txid == f.txid) with
    | none => false
    | some e => !(e.height > 0 && e.height + inFlightDepth ≤ height)
  ({ r with inFlight }, dropped.isSome || inFlight.size != before, dropped)

/-- One transaction of a matched block against one record (`apply(_:at:in:owner:to:discarded:)`): its
spends, its outputs, then the history entry when it touched the account or was already known. -/
def applyTx (tx : Transaction) (txIndex : Nat) (m : Net.BlockMatch) (owner : OwnerMap) (count : UInt32)
    (r : MultisigAccountRecord) : RM (MultisigAccountRecord × Bool × Array ByteArray) := do
  let txid := tx.txid
  let (r, spends) := applySpends tx txid m.height r
  -- A block's first transaction is its coinbase (immature for `Wallet.coinbaseMaturity` blocks).
  let (r, paid, received) ← applyOutputs tx txid owner count m.height (txIndex == 0) r
  let known := r.history.any (·.txid == txid)
  unless spends.spent > 0 || received > 0 || known do return (r, spends.changed || paid, spends.dropped)
  let fee := HistoryLedger.exactFee spends.spent tx spends.allInputsOurs
  let (history, _) := HistoryLedger.record r.history tx txid m.height m.blockHash received spends.spent fee
  -- A block took it, so nothing replaced it: a spend that lost on one branch and confirmed on the next is a spend again.
  let history := history.map fun e => if e.txid == txid then { e with replacedBy := none } else e
  return ({ r with history }, true, spends.dropped)

/-- Consumes one matched block like `Wallet.apply`: payments to account scripts become coins, spends turn
coins into tombstones, and every transaction that touched an account lands in its history through
`HistoryLedger`. The next store, the in-flight spends a conflicting transaction in this block beat (which
can never confirm, so the broadcaster stops relaying them), and the people its drafts paid:
`(personID, paymentIndex)` of each draft whose own transaction this block confirms, whoever broadcast it
(fixed upstream bug 3). -/
def applyPaying (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (m : Net.BlockMatch)
    (network : BitcoinNetwork) : RM (MultisigStore × Array ByteArray × Array (String × UInt32)) := do
  unless network == s.network do invalid "the account network does not match the open wallet"
  -- A damaged store has no records, so nothing here can write over it.
  let mut store := s
  let mut candidate := s.records
  let mut changed := false
  let mut discarded : Array ByteArray := #[]
  let mut paid : Array (String × UInt32) := #[]
  let blockTxids := m.block.transactions.map (·.txid)
  for i in [0:candidate.size] do
    let (cache, store') ← store.ownerCache candidate[i]!
    store := store'
    let owner := cache.owner
    let count := MultisigStore.watchCount candidate[i]!
    let mut r := candidate[i]!
    for h : txIndex in [0:m.block.transactions.size] do
      let (r', touched, lost) ← applyTx m.block.transactions[txIndex] txIndex m owner count r
      r := r'
      discarded := discarded ++ lost
      if touched then changed := true
    let (r', settled, dropped) := settle r m.height
    r := r'
    if settled then changed := true
    if let some d := dropped then
      if let (some person, some index, .ok txid) := (d.personID, d.paymentIndex, d.txid) then
        if blockTxids.contains txid then paid := paid.push (person, index)
    candidate := candidate.set! i r
  unless changed do return (store, #[], #[])
  let (caches, store') ← store.ownerCaches candidate
  validate candidate network caches
  return (← store'.mutate keys writeData candidate, discarded, paid)

/-- `apply(match:network:)`: `applyPaying` without the people paid. -/
def apply (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (m : Net.BlockMatch) (network : BitcoinNetwork) :
    RM (MultisigStore × Array ByteArray) := do
  let (store, discarded, _) ← s.applyPaying keys writeData m network
  return (store, discarded)

/-! ## Spends, addresses, rollbacks -/

/-- Marks the next receive address used ("New address"). -/
def advanceReceiveIndex (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) : RM MultisigStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | return s
  unless s.records[i]!.nextReceiveIndex < maximumNextIndex do invalid "receive address index is out of range"
  s.mutate keys writeData (s.records.modify i fun r => { r with nextReceiveIndex := r.nextReceiveIndex + 1 })

/-- `setLedger(id:registration:)`: files the Ledger registration for an account the Ledger signs for,
once it is this account's own policy and names one of its signers. -/
def setLedger (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String)
    (registration : LedgerRegistration) : RM MultisigStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | invalid "the account is no longer on this phone"
  let updated := { s.records[i]! with ledger := some registration }
  let account ← liftAccount s.network (MultisigAccount.parse updated.descriptor s.network)
  liftAccount s.network (updated.checkLedgerRegistration account)
  s.mutate keys writeData (s.records.set! i updated)

/-- The spend's one output to the account's change address at `changeIndex`, as a pending coin. -/
def pendingChange (tx : Transaction) (account : MultisigAccount) (changeIndex : UInt32) (network : BitcoinNetwork) :
    RM WalletUTXO := do
  unless changeIndex ≤ maximumNextIndex do invalid "change address index is out of range"
  let changeScript ← liftAccount network (account.scriptPubKey changeIndex AddressChain.change.rawValue)
  let found := (List.range tx.outputs.size).filter fun k => tx.outputs[k]!.scriptPubKey == changeScript
  match found with
  | [k] =>
    let o := tx.outputs[k]!
    unless o.value > 0 && o.value.toInt ≤ maximumMoney do invalid "the change output is missing or invalid"
    return { txid := tx.txid, vout := k.toUInt32, amount := o.value, scriptPubKey := changeScript, chain := .change,
             index := changeIndex, height := 0 }
  | _ => invalid "the change output is missing or invalid"

/-- After a spend is broadcast: its inputs become in-flight tombstones at once and the change enters
pending (height 0), the rule `Wallet.commit` applies to the wallet's own coins; the spend lands in history
as pending with its exact fee and breakdown, its bytes are kept for announcing it again, and the draft it
was is retired. False when the spend touches no live coin of the account. -/
def recordSpend (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) (tx : Transaction)
    (changeIndex : Option UInt32) (broadcastHeight : UInt32 := 0) : RM (MultisigStore × Bool) := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | return (s, false)
  let mut r := s.records[i]!
  let account ← liftAccount s.network (MultisigAccount.parse r.descriptor s.network)
  let txid := tx.txid
  let mut spent : Int64 := 0
  let mut reserved := 0
  for input in tx.inputs do
    for k in [0:r.allUtxos.size] do
      let u := r.allUtxos[k]!
      if !u.isSpent && u.outpoint == input.previousOutput then
        -- No height: this spend exists only in the transaction just broadcast.
        r := { r with allUtxos := r.allUtxos.set! k { u with spent := some { spentBy := txid, height := none } } }
        spent := spent + u.amount
        reserved := reserved + 1
  unless reserved > 0 do return (s, false)
  let mut received : Int64 := 0
  if let some ci := changeIndex then
    let change ← pendingChange tx account ci s.network
    r := { r with allUtxos := r.allUtxos.push change, nextChangeIndex := max r.nextChangeIndex (ci + 1) }
    received := change.amount
  -- `recordPendingSpend`: the pending entry and the bytes
  let (cache, s) ← s.ownerCache r
  unless r.history.any (·.txid == txid) do
    let chain := fun (script : ByteArray) => cache.owner[script]?.map fun (choice, _) =>
      if choice == 1 then AddressChain.change else .receive
    let entry : HistoryEntry :=
      { txid, height := 0, received, spent,
        fee := HistoryLedger.exactFee spent tx (reserved == tx.inputs.size),
        rawTransaction := some (tx.serialized false), fundingScripts := FundingSources.fundingScripts tx,
        outputs := some (HistoryLedger.classifyOutputs tx chain) }
    r := { r with history := r.history.push entry, inFlight := r.inFlight.push (InFlightSpend.ofTransaction tx broadcastHeight) }
  r := (pruneDraft r).1
  let candidate := s.records.set! i r
  let (caches, store) ← s.ownerCaches candidate
  validate candidate s.network caches
  return (← store.mutate keys writeData candidate, true)

/-- `setDraft(id:_:)`: files the spend this phone is collecting signatures for, one per account and
spending only its live coins; none discards it. -/
def setDraft (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String)
    (draft : Option MultisigSpendDraft) : RM MultisigStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | invalid "the account is no longer on this phone"
  let candidate := s.records.modify i fun r => { r with draft }
  validate candidate s.network s.ownerMaps
  s.mutate keys writeData candidate

/-- `abandonSpend(id:txid:)`: gives up on a spend this phone broadcast that no block has taken: its inputs
are live again, its pending change and anything chained on it leave, and its entry and bytes go. Refused
once a block has it. -/
def abandonSpend (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) (txid : ByteArray) :
    RM MultisigStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | invalid "the account is no longer on this phone"
  let r := s.records[i]!
  unless r.history.any (fun e => e.txid == txid && e.height == 0) do
    invalid "only a spend no block has confirmed can be given up"
  let (r, dropped) := dropLosingSpends #[txid] r
  let r := { r with history := r.history.filter (!dropped.contains ·.txid), inFlight := r.inFlight.filter (!dropped.contains ·.txid) }
  let candidate := s.records.set! i r
  validate candidate s.network s.ownerMaps
  s.mutate keys writeData candidate

/-- A spend whose block fell is back in every mempool that saw it: its inputs stay reserved for it. -/
def rependSpends (fork : UInt32) (coins : Array WalletUTXO) : Array WalletUTXO :=
  coins.map fun u => match u.spent with
    | some { spentBy, height := some h } => if h > fork then { u with spent := some { spentBy, height := none } } else u
    | _ => u

/-- Coins confirmed above the fork leave (the rescan re-finds them), except one a spend holds, which stays
at height 0. -/
def rewindCoins (fork : UInt32) (coins : Array WalletUTXO) : Array WalletUTXO :=
  let kept := coins.filter fun u => !(u.height > fork && !isPending u)
  kept.map fun u => if u.height > fork then { u with height := 0 } else u

/-- `rollBack(to:)`: coins and history to a fork height, matching `Wallet.rollBack`: spends from fallen blocks
go back in flight (their entries re-pend, their bytes stay), coins from fallen blocks leave unless a spend
holds them, and a draft whose coin fell is dropped. A pure function of the fork height (a repeat changes
nothing); frontiers untouched. -/
def rollBack (s : MultisigStore) (keys : StoreKeyVault) (writeData : WriteData) (fork : UInt32) : RM MultisigStore := do
  let candidate := s.records.map fun r =>
    let r := { r with history := (HistoryLedger.rewind r.history fork).1,
                      allUtxos := rewindCoins fork (rependSpends fork r.allUtxos) }
    (pruneDraft r).1
  if candidate == s.records then return s
  s.mutate keys writeData candidate

end MultisigStore

/-! ## The current store -/

/-- The multisig store of the open network directory, behind one mutex (the Swift actor's isolation). -/
structure MultisigHost where
  keys : StoreKeyVault
  writeData : WriteData := writeAtomically
  state : Std.Mutex MultisigStore
  /-- `multisigStorageNotice`: set when `multisig.json` could not be read. -/
  notice : IO.Ref (Option String)

namespace MultisigHost

def new (keys : StoreKeyVault) (writeData : WriteData := writeAtomically) : IO MultisigHost := do
  return { keys, writeData, state := ← Std.Mutex.new {}, notice := ← IO.mkRef none }

def read (h : MultisigHost) : IO MultisigStore := h.state.atomically get

/-- Runs a mutation under the lock; the store changes only when it succeeds. -/
def modify {α} (h : MultisigHost) (f : MultisigStore → RM (MultisigStore × α)) : RM α :=
  h.state.atomically do
    let s ← get
    let (s', a) ← (f s : RM _)
    set s'
    return a

/-- `configureMultisig()`: reads the file of `dir` (none: unreachable storage, nothing persisted). -/
def configure (h : MultisigHost) (network : BitcoinNetwork) (dir : Option System.FilePath) : IO Unit := do
  let (store, result) ← MultisigStore.configure h.keys (dir.map (· / MultisigStore.fileName)) network
  h.state.atomically (set store)
  h.notice.set (match result with | .damaged m => some m | _ => none)

def all (h : MultisigHost) : IO (Array MultisigAccountRecord) := return (← h.read).records

end MultisigHost

end WinnowApp.RecordsReal
