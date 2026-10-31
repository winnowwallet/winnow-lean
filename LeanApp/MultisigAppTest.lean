import WinnowApp.Real
import WinnowApp.Signers
import WinnowApp.Payments
import WinnowApp.View
import LeanNative.Erase
import LeanNative.Json

/-! `multisig-app-test`: upstream 1cf93fb's app-side multisig tests, ported.

* `AppTests/MultisigStoreTests.swift` (all 10 tests): sealed persistence, backups, and the coin bookkeeping
  the combined filter scan drives (payments, spends, conflicts, reorgs), against `MultisigStore`;
* `AppTests/MultisigAccountFlowTests.swift` without the Ledger: the builder (with another Winnow's key and a
  recovery path), a co-signer's spend signed on two phones with BIP326 sequences, the recovery path's age
  check and the Advanced-mode gate, through `Backend.real` (`Real/Multisig.lean`) on wallets opened from
  disk with no network.

Fixtures as `Tests/Support/TestKeys.swift` (masters from BIP39 over 16 repeated bytes: 0xA1, 0xB2, 0xC3;
0xD4 a recovery key; keys at m/86'/1'/0'). Exits 1 on any failure. -/

open Winnow WinnowApp WinnowApp.RecordsReal
open Tx (BitcoinNetwork)

initialize passed : IO.Ref Nat ← IO.mkRef 0
initialize failures : IO.Ref (Array String) ← IO.mkRef #[]

def check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then passed.modify (· + 1)
  else
    failures.modify (·.push name)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

def need {α} (name : String) (x : RM α) : IO α := do
  match ← x.run with
  | .ok a => return a
  | .error e => throw (IO.userError s!"{name}: {e.name}: {e.description}")

def needM {α} (name : String) (r : MAM α) : IO α := do
  match r with
  | .ok a => return a
  | .error e => throw (IO.userError s!"{name}: {e.name}")

def needE {ε α} (name : String) (r : Except ε α) : IO α := do
  match r with
  | .ok a => return a
  | .error _ => throw (IO.userError s!"{name} failed")

/-- Expects the failure `kind` (any kind when empty). -/
def refused {α} (name : String) (x : RM α) (kind : String := "") : IO Unit := do
  match ← x.run with
  | .ok _ => check name false "accepted"
  | .error e => check name (kind.isEmpty || e.name == kind) s!"got {e.name}: {e.description}"

def runTest (name : String) (t : IO Unit) : IO Unit := do
  -- `MULTISIG_APP_TEST_ONLY=<substring>` runs only the tests whose name contains it
  if let some only ← IO.getEnv "MULTISIG_APP_TEST_ONLY" then
    unless (name.splitOn only).length > 1 do return
  let start ← IO.monoMsNow
  try t catch e =>
    failures.modify (·.push name)
    IO.println s!"FAIL {name} (aborted): {e}"
  IO.println s!"  {name}: {(← IO.monoMsNow) - start} ms"
  (← IO.getStdout).flush

/-! ## Fixtures -/

initialize masterCache : IO.Ref (Array (UInt8 × Keys.HDKey)) ← IO.mkRef #[]

def master (entropyByte : UInt8) : IO Keys.HDKey := do
  if let some (_, m) := (← masterCache.get).find? (·.1 == entropyByte) then return m
  let words ← needE "mnemonic" (Keys.BIP39.mnemonic (ByteArray.mk (Array.replicate 16 entropyByte)))
  let m ← needE "master" (Keys.HDKey.ofSeed (Keys.BIP39.seed words))
  masterCache.modify (·.push (entropyByte, m))
  return m

def masters : IO (Array Keys.HDKey) := #[0xA1, 0xB2, 0xC3].mapM master

def keyExpression (m : Keys.HDKey) : IO String := do
  let account ← needE "account key" (m.derived "m/86'/1'/0'")
  return s!"[{Descriptor.hex8 m.fingerprint}/86'/1'/0']{account.neutered.serialized .testnet}/<0;1>/*"

def signet : BitcoinNetwork := .signet

def twoOfTwo : IO MultisigAccount := do
  let keys ← ((← masters).extract 0 2).mapM keyExpression
  let d ← needM "descriptor" (MultisigAccount.makeDescriptor 2 keys none signet)
  needM "account" (MultisigAccount.make d signet)

def spk (a : MultisigAccount) (index : UInt32) (choice : Nat := 0) : IO ByteArray :=
  needM "scriptPubKey" (a.scriptPubKey index choice)

def zeros (n : Nat) (b : UInt8 := 0) : ByteArray := ByteArray.mk (Array.replicate n b)

def coinbaseInput : Transaction.Input :=
  { previousOutput := ⟨zeros 32, 0xFFFF_FFFF⟩, scriptSig := ByteArray.mk #[0x01], sequence := 0xFFFF_FFFF }

def fakeMatch (height : UInt32) (txs : Array Transaction) : Net.BlockMatch :=
  let header : Net.BlockHeader := {
    version := 2, previousHash := zeros 32, merkleRoot := zeros 32 0xAA, time := 1_700_000_000 + height,
    bits := 0x207F_FFFF, nonce := 0, hash := .empty }
  -- a 32-byte hash, as a real block has (an entry's `blockHash` is coded as 32 bytes)
  { height, blockHash := zeros 32 (height % 251).toUInt8, block := { header := header, transactions := txs } }

/-- A block whose first transaction is a coinbase paying no one we watch. -/
def block (height : UInt32) (txs : Array Transaction) : Net.BlockMatch :=
  let coinbase : Transaction := {
    version := 1, inputs := #[coinbaseInput],
    outputs := #[{ value := 50, scriptPubKey := ByteArray.mk #[0x51] }], locktime := height }
  fakeMatch height (#[coinbase] ++ txs)

def spend (outpoints : Array Transaction.Outpoint) (outputs : Array Transaction.Output) : Transaction :=
  { version := 2, inputs := outpoints.map fun o => { previousOutput := o, scriptSig := .empty, sequence := 0xFFFF_FFFD },
    outputs, locktime := 0 }

def payment (script : ByteArray) (amount : Int64) (from_ : Transaction.Outpoint) (change : Option Transaction.Output := none) :
    Transaction :=
  spend #[from_] (#[{ value := amount, scriptPubKey := script }] ++ change.toArray)

/-- An outpoint of a transaction this store never saw. -/
def foreign (b : UInt8) : Transaction.Outpoint := ⟨zeros 32 b, 0⟩

def elsewhere : ByteArray := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x77)

def coin (a : MultisigAccount) (amount : Int64) (height : UInt32 := 100) : IO WalletUTXO := do
  return { txid := zeros 32 0x5A, vout := 0, amount, scriptPubKey := ← spk a 0, chain := .receive, index := 0, height }

def recordOf (a : MultisigAccount) (coins : Array WalletUTXO) : MultisigAccountRecord :=
  { id := a.id, name := "Phone and desktop", descriptor := a.descriptor.serialized, createdAtHeight := 0,
    nextReceiveIndex := 1, allUtxos := coins }

def memoryKeys : IO StoreKeyVault := do return StoreKeyVault.inMemory (← IO.mkRef {})

initialize tempRoot : IO.Ref System.FilePath ← IO.mkRef (System.FilePath.mk ".")
initialize tempCount : IO.Ref Nat ← IO.mkRef 0

def tempFile (name : String) : IO System.FilePath := do
  let k ← tempCount.modifyGet fun n => (n, n + 1)
  let dir := (← tempRoot.get) / s!"t{k}"
  IO.FS.createDirAll dir
  return dir / name

/-- A store under test: the value, its keys, and the actor-like calls. -/
structure S where
  keys : StoreKeyVault
  ref : IO.Ref MultisigStore

def S.open (keys : StoreKeyVault) (path : Option System.FilePath) (network : BitcoinNetwork := signet) : IO (S × OpenResult) := do
  let (store, r) ← MultisigStore.configure keys path network
  return ({ keys, ref := ← IO.mkRef store }, r)

def S.step {α} (s : S) (f : MultisigStore → RM (MultisigStore × α)) : RM α := do
  let (next, a) ← f (← RM.io s.ref.get)
  RM.io (s.ref.set next)
  return a

def S.stepU (s : S) (f : MultisigStore → RM MultisigStore) : RM Unit := s.step fun st => do return (← f st, ())

def S.all (s : S) : IO (Array MultisigAccountRecord) := return (← s.ref.get).records
def S.fetch (s : S) (id : String) : IO MultisigAccountRecord := do
  let some r := (← s.ref.get).record? id | throw (IO.userError s!"no record {id}")
  return r
def S.add (s : S) (name : String) (a : MultisigAccount) (h : UInt32) : RM MultisigAccountRecord :=
  s.step fun st => st.add s.keys writeAtomically name a h
def S.restore (s : S) (rs : Array MultisigAccountRecord) : RM Unit := s.stepU fun st => st.restore s.keys writeAtomically rs
def S.apply (s : S) (m : Net.BlockMatch) (network : BitcoinNetwork := signet) : RM (Array ByteArray) :=
  s.step fun st => st.apply s.keys writeAtomically m network
def S.recordSpend (s : S) (id : String) (tx : Transaction) (ci : Option UInt32) (broadcastHeight : UInt32 := 0) : RM Bool :=
  s.step fun st => st.recordSpend s.keys writeAtomically id tx ci broadcastHeight
def S.applyPaying (s : S) (m : Net.BlockMatch) : RM (Array (String × UInt32)) :=
  s.step fun st => do
    let (next, _, paid) ← st.applyPaying s.keys writeAtomically m signet
    return (next, paid)
def S.setDraft (s : S) (id : String) (d : Option MultisigSpendDraft) : RM Unit :=
  s.stepU fun st => st.setDraft s.keys writeAtomically id d
def S.abandon (s : S) (id : String) (txid : ByteArray) : RM Unit :=
  s.stepU fun st => st.abandonSpend s.keys writeAtomically id txid
def S.rollBack (s : S) (fork : UInt32) : RM Unit := s.stepU fun st => st.rollBack s.keys writeAtomically fork
def S.backup (s : S) : RM (Array MultisigAccountRecord) := do (← RM.io s.ref.get).backupRecords
def S.watch (s : S) (network : BitcoinNetwork := signet) : RM (Array ByteArray) := s.step fun st => do
  let (scripts, next) ← st.watchScripts network
  return (next, scripts)

def unsealedPayloadOf (data : ByteArray) : ByteArray :=
  if !SealedStoreFile.isSealed data then data else
  match SealedStoreFile.firstNewline data with
  | some nl => data.extract (nl + 1) data.size
  | none => data

def unsealedPayload (path : System.FilePath) : IO ByteArray := do
  return unsealedPayloadOf (← IO.FS.readBinFile path)

def spentOf (r : MultisigAccountRecord) (o : Transaction.Outpoint) : Option SpentMarker :=
  (r.allUtxos.find? (·.outpoint == o)).bind (·.spent)

def marker (by_ : ByteArray) (h : Option UInt32) : Option SpentMarker := some { spentBy := by_, height := h }

/-! ## MultisigStoreTests -/

def testBackupPreservesAccountsAndRejectsChangedOwnership : IO Unit := do
  let keys ← memoryKeys
  let url ← tempFile "multisig.json"
  let a ← twoOfTwo
  let record := recordOf a #[← coin a 80_000]
  let (store, _) ← S.open keys (some url)
  need "restore" (store.restore #[record])
  let backup : ImportBundle := { network := "signet", lastKnownHeight := 100, vaults := some (← need "backup" store.backup) }
  let decoded ← needE "decode" (ImportBundle.decode backup.serialized)
  check "backup: the bundle carries the record" (decoded.vaults == some #[record])
  let (restarted, opened) ← S.open keys (some url)
  check "backup: the store reopens loaded" (opened == .loaded)
  check "backup: the same records" ((← restarted.all) == #[record])
  let changed := { record with allUtxos := record.allUtxos.modify 0 fun u => { u with scriptPubKey := ByteArray.mk #[0x51] } }
  refused "backup: a foreign coin is refused" (restarted.restore #[changed])
  check "backup: the refused restore changed nothing" ((← restarted.all) == #[record])
  let payload ← unsealedPayload url
  let onDisk := (String.fromUTF8? payload).bind fun t =>
    (SwiftJSON.decodeText t (SwiftJSON.asArray MultisigAccountRecord.ofJV)).toOption
  check "backup: the file holds exactly the record" (onDisk == some #[record])

/-- A backup carries what no block has taken yet, so a restored phone keeps waiting for it instead of
forgetting it (upstream inverted this test in #259). -/
def testBackupCarriesPendingAccountPayments : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) none
  let pending := recordOf a #[← coin a 80_000 0]
  need "restore" (store.restore #[pending])
  let backup ← need "backup" store.backup
  let bundle : ImportBundle := { network := "signet", lastKnownHeight := 100, vaults := some backup }
  let decoded ← needE "decode" (ImportBundle.decode bundle.serialized)
  check "the pending account snapshot round-trips through a bundle" (decoded.vaults == some #[pending])

def testPaymentsSpendsAndRollbacks : IO Unit := do
  let keys ← memoryKeys
  let url ← tempFile "multisig.json"
  let a ← twoOfTwo
  let (store, _) ← S.open keys (some url)
  let added ← need "add" (store.add "Shared" a 100)
  let initial ← need "watch" store.watch
  check "receive and change up to the gap limit" (initial.size == 2 * Wallet.gapLimit.toNat)
  let funding := payment (← spk a 0) 60_000 ⟨zeros 32 0x11, 0⟩
  discard <| need "apply 101" (store.apply (block 101 #[funding]))
  let later := payment (← spk a 2) 7_000 ⟨zeros 32 0x12, 0⟩
  discard <| need "apply 102" (store.apply (block 102 #[later]))
  let mut current ← store.fetch added.id
  check "payments: balance" (current.balance == 67_000) s!"{current.balance}"
  check "a payment at index 2 moves the frontier past it" (current.nextReceiveIndex == 3)
  check "no coinbase coin" (!current.utxos.any (·.isCoinbase))
  -- Our own spend, recorded at broadcast: the input is reserved and the change waits at height 0.
  let changeScript ← spk a 0 1
  let sp := payment elsewhere 40_000 ⟨funding.txid, 0⟩ (some { value := 19_000, scriptPubKey := changeScript })
  check "recordSpend touches the coin" (← need "recordSpend" (store.recordSpend added.id sp (some 0)))
  check "a repeated relay changes nothing" (!(← need "recordSpend again" (store.recordSpend added.id sp (some 0))))
  current ← store.fetch added.id
  check "spend recorded: balance" (current.balance == 26_000) s!"{current.balance}"
  check "spend recorded: change frontier" (current.nextChangeIndex == 1)
  -- The spend is in the history as pending, with its exact fee and breakdown, and its bytes are kept.
  match current.history.find? (·.txid == sp.txid) with
  | some e =>
    check "pending entry: height 0, spent, change received, exact fee"
      (e.height == 0 && e.spent == 60_000 && e.received == 19_000 && e.fee == some 1_000)
    check "pending entry: the breakdown" ((e.outputs.map (·.change)) == some #[1] &&
      (e.outputs.map (·.external.map (·.amount))) == some #[40_000])
  | none => check "the spend is in the history" false
  check "its bytes are kept" (current.inFlight.map (·.txid) == #[sp.txid] && current.inFlight[0]!.transaction.toOption == some sp)
  check "history order" (current.history.map (·.txid) == #[funding.txid, later.txid, sp.txid])
  check "a payment from elsewhere: received, no exact fee"
    (current.history[0]!.received == 60_000 && current.history[0]!.height == 101 && current.history[0]!.fee.isNone)
  check "a backup carries the pending spend" ((← need "backup" store.backup) == #[current])
  -- A reorg below the later payment drops it, with its entry, and keeps the in-flight spend's input reserved.
  need "rollBack 101" (store.rollBack 101)
  current ← store.fetch added.id
  check "rollback: balance" (current.balance == 19_000) s!"{current.balance}"
  check "a reorg never costs an address gap" (current.nextReceiveIndex == 3)
  check "rollback: the later payment's entry left" (current.history.map (·.txid) == #[funding.txid, sp.txid])
  -- The spend confirms in place; a reorg below it puts it back in flight and its entry re-pends.
  discard <| need "apply 103" (store.apply (block 103 #[sp]))
  current ← store.fetch added.id
  check "the spend's tombstone is heighted" ((spentOf current ⟨funding.txid, 0⟩).bind (·.height) == some 103)
  check "the change is confirmed" ((current.utxos.find? (·.txid == sp.txid)).map (·.height) == some 103)
  match current.history.find? (·.txid == sp.txid) with
  | some e =>
    check "confirmed in place: height, fee, the breakdown survives"
      (e.height == 103 && e.fee == some 1_000 && (e.outputs.map (·.change)) == some #[1])
  | none => check "confirmed in place" false
  check "confirmed in place, not appended again" (current.history.size == 2)
  check "bytes kept until the block is buried" (current.inFlight.map (·.txid) == #[sp.txid])
  need "rollBack 102" (store.rollBack 102)
  current ← store.fetch added.id
  check "the fallen spend is in flight again" (spentOf current ⟨funding.txid, 0⟩ == marker sp.txid none)
  check "and its change left" (current.balance == 0) s!"{current.balance}"
  check "its entry re-pended" (((current.history.find? (·.txid == sp.txid)).map (·.height)) == some 0)
  check "its bytes still kept" (current.inFlight.map (·.txid) == #[sp.txid])
  -- Buried deep enough, the bytes are no longer kept.
  discard <| need "apply 103 again" (store.apply (block 103 #[sp]))
  for h in [104:104 + MultisigStore.inFlightDepth.toNat] do
    discard <| need s!"apply {h}" (store.apply (block h.toUInt32 #[payment (ByteArray.mk #[0x51]) 1 (foreign h.toUInt8)]))
  current ← store.fetch added.id
  check "buried: no bytes kept" current.inFlight.isEmpty
  check "buried: the entry stays confirmed" (((current.history.find? (·.txid == sp.txid)).map (·.height)) == some 103)
  let (restarted, _) ← S.open keys (some url)
  check "reopened from disk: the same records" ((← restarted.all) == #[current])

def testARollbackKeepsTheInputsOfAFallenSpendReserved : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) (some (← tempFile "multisig.json"))
  let added ← need "add" (store.add "Shared" a 100)
  let funding := payment (← spk a 0) 60_000 (foreign 0x51)
  let other := payment (← spk a 1) 5_000 (foreign 0x52)
  discard <| need "apply 101" (store.apply (block 101 #[funding, other]))
  let fundingCoin : Transaction.Outpoint := ⟨funding.txid, 0⟩
  let sp := payment elsewhere 40_000 fundingCoin (some { value := 19_000, scriptPubKey := ← spk a 0 1 })
  discard <| need "recordSpend" (store.recordSpend added.id sp (some 0))
  discard <| need "apply 103" (store.apply (block 103 #[sp]))
  let mut current ← store.fetch added.id
  check "fallen spend: balance before" (current.balance == 24_000)
  need "rollBack" (store.rollBack 102)
  current ← store.fetch added.id
  check "fallen spend: in flight again" (spentOf current fundingCoin == marker sp.txid none)
  check "only the coin no spend holds can go into a new one" (current.utxos.map (·.outpoint) == #[⟨other.txid, 0⟩])
  check "the change left with its block" (current.balance == 5_000)
  let backup ← need "backup" store.backup
  check "a backup carries the reservation, so a restore cannot double-spend it"
    (((backup[0]?.bind fun r => r.allUtxos.find? (·.outpoint == fundingCoin)).bind (·.spent)) == marker sp.txid none)
  need "rollBack again" (store.rollBack 102)
  check "a rollback redone after a crash changes nothing" ((← store.fetch added.id) == current)
  let discarded ← need "apply 104" (store.apply (block 104 #[sp]))
  check "nothing discarded" discarded.isEmpty
  current ← store.fetch added.id
  check "the reservation takes its height" (spentOf current fundingCoin == marker sp.txid (some 104))
  check "and the change is back" (current.balance == 24_000)

def testARollbackKeepsAReservedCoinFromAFallenBlock : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) (some (← tempFile "multisig.json"))
  let added ← need "add" (store.add "Shared" a 100)
  let funding := payment (← spk a 0) 60_000 (foreign 0x61)
  discard <| need "apply 101" (store.apply (block 101 #[funding]))
  let first := payment elsewhere 40_000 ⟨funding.txid, 0⟩ (some { value := 19_000, scriptPubKey := ← spk a 0 1 })
  let changeCoin : Transaction.Outpoint := ⟨first.txid, 1⟩
  let second := payment elsewhere 18_000 changeCoin
  discard <| need "apply 103" (store.apply (block 103 #[first]))
  discard <| need "apply 104" (store.apply (block 104 #[second]))
  need "rollBack" (store.rollBack 102)
  let mut current ← store.fetch added.id
  match current.allUtxos.find? (·.outpoint == changeCoin) with
  | some kept =>
    check "the reserved row stays, not in a block yet" (kept.height == 0)
    check "reserved for the second spend" (kept.spent == marker second.txid none)
  | none => check "the reserved row stays" false
  check "reserved coin: balance 0" (current.balance == 0)
  discard <| need "apply 103 again" (store.apply (block 103 #[first]))
  current ← store.fetch added.id
  check "the change is re-heighted, not admitted twice"
    ((current.allUtxos.filter (·.outpoint == changeCoin)).map (·.height) == #[103])
  check "the change is still the second spend's" (current.balance == 0)
  discard <| need "apply 104 again" (store.apply (block 104 #[second]))
  current ← store.fetch added.id
  check "the second spend confirms" (spentOf current changeCoin == marker second.txid (some 104))
  check "nothing pending" (!current.allUtxos.any fun u => u.height == 0 || MultisigStore.isPending u)

def testZeroValueOutputIsIgnoredAndTheScanMovesOn : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) (some (← tempFile "multisig.json"))
  let added ← need "add" (store.add "Shared" a 100)
  let dust := spend #[foreign 0x21] #[{ value := 0, scriptPubKey := ← spk a 1 }, { value := 5_000, scriptPubKey := ← spk a 0 }]
  discard <| need "apply 101" (store.apply (block 101 #[dust]))
  let mut current ← store.fetch added.id
  check "the zero-value output is not a coin" (current.allUtxos.map (·.amount) == #[5_000])
  check "and does not use up its address" (current.nextReceiveIndex == 1)
  let later := payment (← spk a 1) 7_000 (foreign 0x22)
  discard <| need "apply 102" (store.apply (block 102 #[later]))
  current ← store.fetch added.id
  check "the scan moves on" (current.balance == 12_000 && current.nextReceiveIndex == 2)

def testALosingInFlightSpendReleasesItsCoinsAndDropsItsChange : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) (some (← tempFile "multisig.json"))
  let added ← need "add" (store.add "Shared" a 100)
  let first := payment (← spk a 0) 60_000 (foreign 0x31)
  let second := payment (← spk a 1) 30_000 (foreign 0x32)
  discard <| need "apply 101" (store.apply (block 101 #[first, second]))
  let firstCoin : Transaction.Outpoint := ⟨first.txid, 0⟩
  let secondCoin : Transaction.Outpoint := ⟨second.txid, 0⟩
  let ours := spend #[firstCoin, secondCoin] #[{ value := 70_000, scriptPubKey := elsewhere }, { value := 19_000, scriptPubKey := ← spk a 0 1 }]
  discard <| need "recordSpend ours" (store.recordSpend added.id ours (some 0))
  let chained := payment elsewhere 10_000 ⟨ours.txid, 1⟩ (some { value := 8_000, scriptPubKey := ← spk a 1 1 })
  discard <| need "recordSpend chained" (store.recordSpend added.id chained (some 1))
  let mut current ← store.fetch added.id
  check "losing spend: balance before" (current.balance == 8_000) s!"{current.balance}"
  let theirs := payment elsewhere 45_000 firstCoin (some { value := 14_000, scriptPubKey := ← spk a 0 1 })
  let discarded ← need "apply theirs" (store.apply (block 102 #[theirs]))
  check "the broadcaster stops relaying both" (discarded == #[ours.txid, chained.txid])
  current ← store.fetch added.id
  check "the winner holds the coin" (spentOf current firstCoin == marker theirs.txid (some 102))
  let live := current.utxos.map (·.outpoint)
  check "the coins left" (live.size == 2 && live.contains secondCoin && live.contains ⟨theirs.txid, 1⟩)
  check "losing spend: balance after" (current.balance == 44_000) s!"{current.balance}"
  check "the losing spends' outputs never existed" (!current.allUtxos.any fun u => u.txid == ours.txid || u.txid == chained.txid)
  check "nothing stays reserved" (!current.allUtxos.any MultisigStore.isPending)
  let entry (t : ByteArray) := current.history.find? (·.txid == t)
  check "the losing spend stays listed beside the one that took its coin" (((entry ours.txid).bind (·.replacedBy)) == some theirs.txid)
  check "the chained one too" (((entry chained.txid).bind (·.replacedBy)) == some theirs.txid)
  check "nothing is left to announce" current.inFlight.isEmpty
  check "the winner: spent and an exact fee" (((entry theirs.txid).map (·.spent)) == some 60_000 &&
    ((entry theirs.txid).bind (·.fee)) == some 1_000)
  need "rollBack 101" (store.rollBack 101)
  current ← store.fetch added.id
  check "the winner is back in flight" (spentOf current firstCoin == marker theirs.txid none)
  check "its change left with the block" (current.balance == 30_000) s!"{current.balance}"
  let beaten ← need "apply ours" (store.apply (block 102 #[ours]))
  check "ours beats it on the new branch" (beaten == #[theirs.txid])
  current ← store.fetch added.id
  check "ours confirmed: the change" (current.utxos.map (·.outpoint) == #[⟨ours.txid, 1⟩] && current.balance == 19_000)
  let entry (t : ByteArray) := current.history.find? (·.txid == t)
  check "ours won after all" (((entry ours.txid).bind (·.replacedBy)).isNone)
  check "theirs is now the replaced one" (((entry theirs.txid).bind (·.replacedBy)) == some ours.txid)

/-- A creator's PSBT for `sp`, as the draft a phone files. -/
def psbtFor (sp : Transaction) (coins : Array WalletUTXO) : IO PSBT :=
  needE "psbt" (PSBT.create sp
    (sp.inputs.map fun i =>
      let c := coins.find? (·.outpoint == i.previousOutput)
      ({ spentOutput := { amount := (c.map (·.amount)).getD 1, scriptPubKey := (c.map (·.scriptPubKey)).getD (ByteArray.mk #[0x51]) } } : PSBT.InputInfo))
    (sp.outputs.map fun _ => {}))

def draftFor (sp : Transaction) (coins : Array WalletUTXO) (height : UInt32) (person : Option String := none)
    (index : Option UInt32 := none) : IO MultisigSpendDraft := do
  needE "draft" (MultisigSpendDraft.ofPSBT (← psbtFor sp coins) height person index)

/-- A draft lives on the record until its coins are gone: this phone broadcasting it, a co-signer's
conflicting spend confirming, or a reorg taking a coin all drop it. A spend given up on frees its coins. -/
def testDraftsFollowTheirCoinsAndAnAbandonedSpendFreesThem : IO Unit := do
  let keys ← memoryKeys
  let url ← tempFile "multisig.json"
  let a ← twoOfTwo
  let (store, _) ← S.open keys (some url)
  let added ← need "add" (store.add "Shared" a 100)
  let funding := payment (← spk a 0) 60_000 (foreign 0x71)
  discard <| need "apply 101" (store.apply (block 101 #[funding]))
  let fundingCoin : Transaction.Outpoint := ⟨funding.txid, 0⟩
  let sp := payment elsewhere 40_000 fundingCoin (some { value := 19_000, scriptPubKey := ← spk a 0 1 })
  let coins := (← store.fetch added.id).allUtxos
  let draft ← draftFor sp coins 101 (some "bob") (some 3)
  check "a draft's text is BIP174 v0" (draft.psbtBase64.startsWith "cHNidP8BA") draft.psbtBase64
  -- Filed, read back from disk, and carried by a backup.
  need "setDraft" (store.setDraft added.id (some draft))
  check "filed" ((← store.fetch added.id).draft == some draft)
  let (restarted, _) ← S.open keys (some url)
  check "read back from disk" ((← restarted.fetch added.id).draft == some draft)
  check "carried by a backup" (((← need "backup" store.backup)[0]?.bind (·.draft)) == some draft)
  -- A draft of a coin the account does not hold is refused.
  let stranger ← draftFor (payment elsewhere 1 (foreign 0x72)) #[] 101
  refused "a draft of a foreign coin" (store.setDraft added.id (some stranger)) "invalidState"
  -- Broadcast: the draft is retired with the coin it spent...
  discard <| need "recordSpend" (store.recordSpend added.id sp (some 0) 102)
  let mut current ← store.fetch added.id
  check "broadcast: the draft retired" current.draft.isNone
  check "broadcast: the height kept" (current.inFlight.map (·.broadcastHeight) == #[102])
  -- ...and given up on, everything it took is back.
  need "abandon" (store.abandon added.id sp.txid)
  current ← store.fetch added.id
  check "given up: the coin is live" (current.utxos.map (·.outpoint) == #[fundingCoin] && current.balance == 60_000)
  check "given up: its entry and bytes gone" (current.history.map (·.txid) == #[funding.txid] && current.inFlight.isEmpty)
  refused "a confirmed transaction cannot be given up" (store.abandon added.id funding.txid) "invalidState"
  -- Filed again, then a co-signer's spend of the same coin confirms: the draft goes.
  need "setDraft again" (store.setDraft added.id (some draft))
  let theirs := payment elsewhere 50_000 fundingCoin
  let paid ← need "apply theirs" (store.applyPaying (block 103 #[theirs]))
  current ← store.fetch added.id
  check "a co-signer's other spend: the draft goes" current.draft.isNone
  check "a co-signer's other spend paid nobody of the draft" paid.isEmpty
  check "and is in the history" (current.history.map (·.txid) == #[funding.txid, theirs.txid])
  -- And one whose coin a reorg takes away goes with it.
  need "rollBack 102" (store.rollBack 102)
  let late := payment (← spk a 1) 9_000 (foreign 0x73)
  discard <| need "apply late" (store.apply (block 103 #[late]))
  let lateDraft ← draftFor (payment elsewhere 8_000 ⟨late.txid, 0⟩) (← store.fetch added.id).allUtxos 103
  need "setDraft late" (store.setDraft added.id (some lateDraft))
  need "rollBack 102 again" (store.rollBack 102)
  check "a reorg took its coin: the draft goes" (← store.fetch added.id).draft.isNone

/-- Fixed upstream bug 3: the person a draft pays has their address index advanced when the draft's own
transaction confirms, whoever broadcast it; a different spend of the coin pays nobody. -/
def testADraftConfirmedByACoSignerPaysItsPerson : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) none
  let added ← need "add" (store.add "Shared" a 100)
  let funding := payment (← spk a 0) 60_000 (foreign 0x81)
  discard <| need "apply 101" (store.apply (block 101 #[funding]))
  let fundingCoin : Transaction.Outpoint := ⟨funding.txid, 0⟩
  let sp := payment elsewhere 40_000 fundingCoin (some { value := 19_000, scriptPubKey := ← spk a 0 1 })
  need "setDraft" (store.setDraft added.id (some (← draftFor sp (← store.fetch added.id).allUtxos 101 (some "bob") (some 3))))
  -- the co-signer broadcast it (this phone never did): its block reaches this phone
  let paid ← need "apply" (store.applyPaying (block 102 #[sp]))
  check "the draft's own transaction confirming pays Bob at index 3" (paid == #[("bob", 3)])
  check "the draft is gone" (← store.fetch added.id).draft.isNone

def testLookaheadFindsPaymentsUpToTheGapLimitAhead : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) none
  let added ← need "add" (store.add "Shared" a 100)
  let last := Wallet.gapLimit - 1
  let watched ← need "watch" store.watch
  check "watches the last receive index" (watched.contains (← spk a last))
  check "watches the last change index" (watched.contains (← spk a last 1))
  check "not past the gap limit" (!watched.contains (← spk a Wallet.gapLimit))
  discard <| need "apply 101" (store.apply (block 101 #[payment (← spk a last) 9_000 (foreign 0x41)]))
  let mut current ← store.fetch added.id
  check "lookahead: the far payment" (current.balance == 9_000 && current.nextReceiveIndex == Wallet.gapLimit)
  let furthest := 2 * Wallet.gapLimit - 1
  let receive := payment (← spk a furthest) 3_000 (foreign 0x42)
  let toChange := payment (← spk a furthest 1) 2_000 (foreign 0x43)
  discard <| need "apply 102" (store.apply (block 102 #[receive, toChange]))
  current ← store.fetch added.id
  check "the window moved with the frontier" (current.balance == 14_000 &&
    current.nextReceiveIndex == 2 * Wallet.gapLimit && current.nextChangeIndex == 2 * Wallet.gapLimit)

def testTamperedUnsealedAndOversizedFilesAreRefusedAndKept : IO Unit := do
  let keys ← memoryKeys
  let url ← tempFile "multisig.json"
  let a ← twoOfTwo
  let (store, _) ← S.open keys (some url)
  discard <| need "add" (store.add "Shared" a 100)
  check "the file is sealed" (SealedStoreFile.isSealed (← IO.FS.readBinFile url))
  check "the key is established" (((← (keys.key "multisig.signet").run).toOption.join).isSome)
  -- One payload byte changed: the seal refuses it, and nothing is written.
  let bytes ← IO.FS.readBinFile url
  let some i := (List.range bytes.size).reverse.find? (bytes[·]! == 'S'.toNat.toUInt8) | throw (IO.userError "no S")
  let tamperedBytes := bytes.set! i 'T'.toNat.toUInt8
  IO.FS.writeBinFile url tamperedBytes
  let (tampered, r) ← S.open keys (some url)
  check "a tampered account file is not read" (r == .damaged MultisigStore.unverifiedStorageMessage)
  refused "a damaged store accepts no change" (tampered.add "Other" a 1) "damaged"
  check "the damaged file is left as it was" ((← IO.FS.readBinFile url) == tamperedBytes)
  -- A well-formed but unsealed file, on a phone that never sealed one.
  let planted ← tempFile "multisig.json"
  IO.FS.writeBinFile planted (MultisigStore.encode #[recordOf a #[]])
  let (_, r2) ← S.open (← memoryKeys) (some planted)
  check "an unsealed account file is not adopted" (r2 == .damaged MultisigStore.unverifiedStorageMessage)
  let oversized ← tempFile "multisig.json"
  let h ← IO.FS.Handle.mk oversized .write
  h.truncate
  h.write (zeros (MultisigStore.maximumFileBytes + 1))
  h.flush
  let (_, r3) ← S.open keys (some oversized)
  check "an oversized account file is not read" (r3 == .damaged MultisigStore.damagedStorageMessage)

def testDuplicateWrongNetworkAndBadNamesAreRefused : IO Unit := do
  let a ← twoOfTwo
  let (store, _) ← S.open (← memoryKeys) (some (← tempFile "multisig.json"))
  discard <| need "add" (store.add "Shared" a 1)
  refused "the same account twice" (store.add "Again" a 1) "duplicate"
  let regtest ← needM "regtest account" (MultisigAccount.make a.descriptor .regtest)
  refused "another network's account" (store.add "Regtest" regtest 1) "invalidState"
  for name in ["", "two\nlines", String.ofList (List.replicate (DisplayName.maximumLength + 1) 'x')] do
    let (fresh, _) ← S.open (← memoryKeys) none
    refused s!"an unusable name ({name.length} characters)" (fresh.add name a 1) "invalidState"
  check "one account" ((← store.all).size == 1)


/-! ## MultisigAccountFlowTests (no Ledger) -/

/-- A ready phone (`readyMultisigModel`): a signet wallet created from one repeated entropy byte in its own
directory, opened by `Backend.real` with no network. -/
structure Phone where
  backend : Backend
  env : Real.Env
  multisig : Real.MultisigApp

def phoneWith (entropyByte : UInt8) : IO Phone := do
  let dir := (← tempFile "wallet.json").parent.get!
  let secrets ← IO.mkRef ({} : Keys.InMemorySecrets)
  let ks := Winnow.inMemoryKeyStore secrets
  match ← (Wallet.create .signet ks (some (dir / "wallet.json")) (entropy := some (zeros 16 entropyByte))).run with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"Wallet.create: {e.name}")
  let (backend, env, multisig) ← Backend.realWithMultisig { keyStore := ks, fetch := fun _ => throw (.other "offline") }
  let r ← backend.openWallet .signet dir.toString
  check "the phone boots ready" (r matches .opened _)
  return { backend, env, multisig }

def failsWith {α} (name : String) (x : IO α) (text : String) : IO Unit := do
  match ← (x.toBaseIO) with
  | .ok _ => check name false "accepted"
  | .error e => check name (toString e == text) s!"got {e}"

def Phone.keyExpression (p : Phone) : IO String := Real.multisigKeyExpression p.env
def Phone.record (p : Phone) (id : String) : IO MultisigAccountRecord := Real.record p.multisig id
def Phone.accounts (p : Phone) : IO (List MultisigInfo) := do return (← p.backend.multisigOverview).accounts

/-- `createMultisigAccount(name:threshold:members:recovery:)` (Advanced mode): id and descriptor. -/
def Phone.build (p : Phone) (name : String) (threshold : Nat) (members : List (List String))
    (recovery : Option MultisigRecovery := none) (advanced := true) : IO (String × String) := do
  let (id, d, _) ← p.backend.createMultisigAccount advanced name threshold (members.map (·, none)) recovery
  return (id, d)

/-- This phone and the other keys, each a member of its own. -/
def Phone.buildWith (p : Phone) (name : String) (threshold : Nat) (others : List String)
    (recovery : Option MultisigRecovery := none) (advanced := true) : IO (String × String) := do
  p.build name threshold ([← p.keyExpression] :: others.map ([·])) recovery advanced

def Phone.join (p : Phone) (name descriptor : String) : IO String := do
  return (← p.backend.addMultisigAccount true name descriptor).1

def testBuilderMakesAccountWithAnotherWinnowAndRecovery : IO Unit := do
  let phone ← phoneWith 0xA1
  let ms ← masters
  let otherWinnow ← keyExpression ms[2]!
  let (id, descriptor) ← phone.buildWith "Family 2-of-2" 2 [s!" {otherWinnow} "] (some (.fewerSigners 1 4320))
  let account ← needM "account" (MultisigAccount.parse descriptor signet)
  check "builder: 2 of 2 with a recovery path of 1 after 4320 blocks" (account.threshold == 2 && account.signers.size == 2 &&
    (account.recovery.map (·.blocks)) == some 4320 && (account.recovery.map (·.threshold)) == some 1)
  check "builder: the record is the account" (id == account.id)
  let otherKey ← needE "other account key" (ms[2]!.derived "m/86'/1'/0'")
  check "the other Winnow's key is a signer" (account.includes otherKey.neutered)
  -- The same account with this phone's recovery copy under another fingerprint (SEC-037).
  let phoneKey ← phone.keyExpression
  let bare := (phoneKey.dropEnd "/<0;1>/*".length).copy
  let body := (descriptor.splitOn "#")[0]!
  let relabelled := body.replace (bare ++ "/<2;3>/*") ("[deadbeef" ++ (bare.drop 9).copy ++ "/<2;3>/*")
  check "the relabelled descriptor differs" (relabelled != body)
  failsWith "joining refuses a recovery leaf that relabels a signer" (phone.join "Relabelled" relabelled)
    (MultisigAccountError.invalidDescriptor "a signer reused for recovery must keep its own fingerprint and path there").description
  check "one account" ((← phone.accounts).length == 1)
  -- Phone and another Winnow with a separate recovery key.
  let recoveryKey ← keyExpression (← master 0xD4)
  let (_, pair) ← phone.buildWith "Two phones" 2 [otherWinnow] (some (.separateKey recoveryKey 144))
  let pairAccount ← needM "pair" (MultisigAccount.parse pair signet)
  check "a separate recovery key" ((pairAccount.recovery.map (·.keys.size)) == some 1)
  check "two accounts" ((← phone.accounts).length == 2)
  let info := (← phone.accounts).find? (·.id == id)
  check "the overview: policy and recovery text" ((info.bind (·.policy)) == some "2 of 2" &&
    (info.bind (·.recovery)) == some "after 4320 blocks: any 1 of the signers")
  let pairInfo := (← phone.accounts).find? (·.name == "Two phones")
  check "the overview: a separate recovery key" ((pairInfo.bind (·.recovery)) == some "after 144 blocks: the recovery key")

def fundingTx (seed : UInt8) (script : ByteArray) : Transaction :=
  spend #[⟨zeros 32 seed, 0⟩] #[{ value := 60_000, scriptPubKey := script }]

def coinbaseAt (height : UInt32) : Transaction := {
  version := 1, inputs := #[coinbaseInput],
  outputs := #[{ value := 50, scriptPubKey := ByteArray.mk #[0x51] }], locktime := height }

def testTwoPhonesSignACoSignersSpendWithBIP326Sequences : IO Unit := do
  let phone ← phoneWith 0xA1
  let otherPhone ← phoneWith 0xC3
  let recoveryKey ← keyExpression (← master 0xD4)
  let (id, descriptor) ← phone.buildWith "Two phones" 2 [← otherPhone.keyExpression]
    (some (.separateKey recoveryKey 144))
  let otherID ← otherPhone.join "Two phones" descriptor
  check "the other phone joins the same account" (otherID == id)
  let account ← needM "account" (MultisigAccount.parse descriptor signet)
  let created ← phone.record id
  -- Two coins 300 blocks apart reach both phones.
  let height := created.createdAtHeight + 1
  let mut coins : Array Transaction := #[]
  for (offset, index) in [((0 : UInt32), (0 : UInt32)), (300, 1)] do
    let funding := fundingTx (0x35 + index.toUInt8) (← spk account index)
    coins := coins.push funding
    for p in [phone, otherPhone] do
      discard <| p.multisig.applyMatch (fakeMatch (height + offset) #[coinbaseAt (height + offset), funding]) signet
  let record ← phone.record id
  check "both coins credited" (record.balance == 120_000) s!"{record.balance}"
  check "the overview shows the balance" (((← phone.accounts).find? (·.id == id)).map (·.balance) == some 120_000)
  -- A co-signer's wallet sets each input's sequence to its coin's confirmations (BIP326): one meets the
  -- 144-block recovery lock, one does not. Both phones take it as the signers' path.
  let destination ← do
    let d ← needE "destination descriptor" (Descriptor.parse s!"tr({← keyExpression (← masters)[1]!})")
    pure ((← needE "derived" (d.derived 0 signet))[0]!.address)
  let created ← Real.createMultisigSpend phone.env phone.multisig id destination 100_000 2.0 false
  let proposal ← needE "proposal" (PSBT.ofBase64 created.psbt)
  let tx ← needE "unsigned" proposal.unsignedTransaction
  let mut edited := proposal
  for h : k in [0:tx.inputs.size] do
    let seq : UInt32 := if tx.inputs[k].previousOutput.txid == coins[0]!.txid then 305 else 5
    edited := { edited with inputs := edited.inputs.modify k (·.setSequence (some seq)) }
  let proposalText := edited.base64
  for p in [phone, otherPhone] do
    let shown ← Real.reviewMultisigPSBT p.env p.multisig id proposalText
    check "the signers' path only" ((shown.screen.map (·.signatures.map (·.1))) == some [false]) s!"{shown.reviewError}"
    check "this phone has not signed" ((shown.screen.map (·.progress.phoneUnsigned)) == some true)
  let mine ← Real.signMultisigSpend phone.env phone.multisig id proposalText
  let theirs ← Real.signMultisigSpend otherPhone.env otherPhone.multisig id proposalText
  check "one signature after signing here" ((mine.screen.map (·.signatures)) == some [(false, 1, 2)])
  check "signed here: share it" ((mine.screen.map (·.progress.nextStep)) ==
    some "Share the PSBT below with the other signers, then combine their signed copies here.")
  let combined ← Real.addPastedPSBT phone.env phone.multisig id (some mine.psbt) theirs.output.get!
  check "combined: complete" ((combined.screen.map (·.progress.complete)) == some true)
  check "combined: next step" ((combined.screen.map (·.progress.nextStep)) == some "Enough signatures verify. Finalize and broadcast.")
  let full ← needE "combined psbt" (PSBT.ofBase64 combined.psbt)
  let (_, final) ← needM "finalize" (account.finalizeSpend full record.utxos (Real.ownedCoordinates record) (height + 304))
  check "the BIP326 sequences survive" ((final.inputs.map (·.sequence)).qsort (· < ·) == #[5, 305])

def testRecoveryPathRefusesCoinsThatAreTooYoung : IO Unit := do
  let phone ← phoneWith 0xA1
  let (id, descriptor) ← phone.buildWith "Two phones" 2 [← keyExpression (← masters)[2]!]
    (some (.fewerSigners 1 1000))
  let account ← needM "account" (MultisigAccount.parse descriptor signet)
  let height := (← phone.record id).createdAtHeight + 1
  discard <| phone.multisig.applyMatch (fakeMatch height #[coinbaseAt height, fundingTx 0x34 (← spk account 0)]) signet
  let destination ← do
    let d ← needE "destination descriptor" (Descriptor.parse s!"tr({← keyExpression (← masters)[0]!})")
    pure ((← needE "derived" (d.derived 5 signet))[0]!.address)
  match ← (Real.createMultisigSpend phone.env phone.multisig id destination 20_000 2.0 true).toBaseIO with
  | .ok _ => check "a coin younger than the recovery delay is not offered to the recovery path" false
  | .error e =>
    check "a coin younger than the recovery delay is not offered to the recovery path"
      ((toString e).startsWith "This multisig spend is unsafe:") (toString e)
  match ← (Real.createMultisigSpend phone.env phone.multisig id destination 20_000 2.0 false).toBaseIO with
  | .ok p => check "the signers' path spends it at once" p.screen.isSome
  | .error e => check "the signers' path spends it at once" false (toString e)

def testBuilderIsAdvancedModeOnly : IO Unit := do
  let phone ← phoneWith 0xA1
  failsWith "the builder refuses Simple mode"
    (phone.buildWith "Two phones" 2 [← keyExpression (← masters)[2]!] (advanced := false)) Real.advancedModeOnlyText

def flowTests : List (String × IO Unit) :=
  [ ("testBuilderMakesAccountWithAnotherWinnowAndRecovery", testBuilderMakesAccountWithAnotherWinnowAndRecovery)
  , ("testTwoPhonesSignACoSignersSpendWithBIP326Sequences", testTwoPhonesSignACoSignersSpendWithBIP326Sequences)
  , ("testRecoveryPathRefusesCoinsThatAreTooYoung", testRecoveryPathRefusesCoinsThatAreTooYoung)
  , ("testBuilderIsAdvancedModeOnly", testBuilderIsAdvancedModeOnly) ]


/-! ## LedgerPairingTests and LedgerBluetoothTests -/

/-- `SimulatorConnector`: the phone's Ledger is the simulator; `relabelsLeaves` rewrites the leaf hash in
every signature the device yields, as a faulty or tampered device or link would. -/
def Phone.useLedger (p : Phone) (device : IO.Ref Ledger.Simulator) (relabelsLeaves : Bool := false) : IO Unit :=
  p.multisig.ledger.set do
    let base ← Real.simulatedLedger device
    if !relabelsLeaves then return base
    return { base with exchange := fun apdu => do
      let reply ← base.exchange apdu
      -- a yielded script-path signature: tag, input, key length 64, x-only key, leaf hash, signature
      if reply.size > 70 && reply[0]! == 0x10 && reply[2]! == 64 && reply[reply.size - 2]! == 0xE0 && reply[reply.size - 1]! == 0x00 then
        return reply.extract 0 35 ++ zeros 32 0xEE ++ reply.extract 67 reply.size
      return reply }

def simulator (entropyByte : UInt8) : IO (IO.Ref Ledger.Simulator) := do
  IO.mkRef (Ledger.Simulator.new (← master entropyByte))

/-- `buildWithLedger`: pairs the simulator as "Nano X" and builds `threshold` of this phone, `otherKeys` and
the Ledger, which then registers the account (the builder's registration step). -/
def Phone.buildWithLedger (p : Phone) (name : String) (otherKeys : List String := []) (threshold := 2)
    (recovery : Option MultisigRecovery := none) : IO (String × String × Option (Except String String)) := do
  let ledgerID ← p.backend.pairLedger true "Nano X"
  let some ledger := (← p.backend.multisigOverview).signers.find? (·.id == ledgerID) | throw (IO.userError "no Ledger")
  p.backend.createMultisigAccount true name threshold
    (([← p.keyExpression] :: otherKeys.map ([·]) ++ [ledger.keys]).map (·, none)) recovery

def testLedgerSigningIsAdvancedModeOnly : IO Unit := do
  let phone ← phoneWith 0xA1
  phone.useLedger (← simulator 0xB2)
  failsWith "pairing refuses Simple mode" (phone.backend.pairLedger false "Nano X") Real.advancedModeOnlyText
  check "no signer" (← phone.backend.multisigOverview).signers.isEmpty
  check "no account" (← phone.accounts).isEmpty

def screenOf (p : MultisigPSBT) : IO MultisigScreen := do
  let some s := p.screen | throw (IO.userError s!"no review: {p.reviewError}")
  return s

def testPairVerifyAndSpendWithBothSigners : IO Unit := do
  let phone ← phoneWith 0xA1
  let device ← simulator 0xB2
  phone.useLedger device
  -- Pairing files the Ledger among the signers; nothing is registered yet.
  let ledgerID ← phone.backend.pairLedger true "Nano X"
  let some ledger := (← phone.backend.multisigOverview).signers.find? (·.id == ledgerID) | throw (IO.userError "no Ledger")
  check "paired: a Ledger signer" (ledger.isLedger && ledger.keysText == Descriptor.hex8 (← master 0xB2).fingerprint)
  check "nothing registered by pairing" (← device.get).registeredNames.isEmpty
  let againID ← phone.backend.pairLedger true "Nano X, renamed"
  check "pairing again renames it" (againID == ledgerID &&
    (← phone.backend.multisigOverview).signers.map (·.name) == ["Nano X, renamed"])
  -- The 2-of-2 of this phone and the Ledger, which the Ledger then approves.
  let members := [[← phone.keyExpression], ledger.keys]
  let (id, _, registration) ← phone.backend.createMultisigAccount true "Phone and Ledger" 2 (members.map (·, none)) none
  check "the paired Ledger approved it" (registration matches some (.ok "Nano X, renamed"))
  let record ← phone.record id
  let account ← needM "account" (MultisigAccount.parse record.descriptor signet)
  check "paired: 2 of 2" (account.threshold == 2 && account.signers.size == 2 && !account.isNested)
  let ledgerFingerprint := (← master 0xB2).fingerprint
  check "the registration names the Ledger's master and BIP87 path" (match record.ledger with
    | some r => r.masterFingerprint == ledgerFingerprint && r.keyPath == Ledger.Multisig.keyPath .signet
    | none => false)
  check "the Ledger approved the account by name" ((← device.get).registeredNames == #["Phone and Ledger"])
  check "the account names the Ledger" ((((← phone.accounts).find? (·.id == id)).bind (·.ledgerName)) ==
    some s!"Nano X, renamed · {Descriptor.hex8 (← master 0xB2).fingerprint}")
  -- Building the same account again yields it rather than a copy, and registers no further.
  let (same, _, again) ← phone.backend.createMultisigAccount true "Phone and Ledger" 2 (members.map (·, none)) none
  check "building again yields the same account" (same == id && (← phone.accounts).length == 1)
  check "a registered account registers no further" (again.isNone && (← device.get).registeredNames.size == 1)
  let shown ← phone.backend.verifyLedgerAddress true id 0
  check "the Ledger shows the phone's first address" ((account.address 0).toOption == some shown)
  check "on its screen" ((← device.get).displayedAddresses == #[shown])
  check "the account screen shows the Ledger" (((← phone.accounts).find? (·.id == id)).bind (·.ledgerFingerprint) ==
    some (Descriptor.hex8 (← master 0xB2).fingerprint))
  -- Fund the account, then spend: the phone and the Ledger each sign.
  let height := record.createdAtHeight + 1
  discard <| phone.multisig.applyMatch (fakeMatch height #[coinbaseAt height, fundingTx 0x33 (← spk account 0)]) signet
  let record ← phone.record id
  check "funded" (record.balance == 60_000)
  let destination ← do
    let d ← needE "destination descriptor" (Descriptor.parse s!"tr({← keyExpression (← masters)[2]!})")
    pure ((← needE "derived" (d.derived 0 signet))[0]!.address)
  let created ← Real.createMultisigSpend phone.env phone.multisig id destination 40_000 2.0 false
  let screen ← screenOf created
  check "before signing: the signers' path, nothing signed" (screen.signatures == [(false, 0, 2)])
  check "both still to sign" (screen.progress == { phoneHolds := true, phoneUnsigned := true, ledgerHolds := true, ledgerUnsigned := true })
  check "the footer asks for both" (screen.progress.nextStep.startsWith "Add this phone's signature and the Ledger's")
  let byLedger ← Real.signMultisigSpendWithLedger phone.env phone.multisig true id created.psbt
  let screen ← screenOf byLedger
  check "the Ledger's signature verifies" (screen.signatures == [(false, 1, 2)] && !screen.progress.ledgerUnsigned && !screen.progress.complete)
  check "then the footer asks for the phone" (screen.progress.nextStep ==
    "Check the payment, then add this phone's signature. Signers can sign in any order.")
  -- A device whose signatures name a leaf they were not made for is refused (SEC-036), nothing added.
  phone.useLedger device (relabelsLeaves := true)
  failsWith "a relabelled Ledger signature is refused" (Real.signMultisigSpendWithLedger phone.env phone.multisig true id byLedger.psbt)
    (LedgerError.mismatch "a Ledger signature does not verify").description
  phone.useLedger device
  let both ← Real.signMultisigSpend phone.env phone.multisig id byLedger.psbt
  let screen ← screenOf both
  check "both signed: complete" (screen.signatures == [(false, 2, 2)] && screen.progress.complete &&
    screen.progress.nextStep == "Enough signatures verify. Finalize and broadcast.")
  let full ← needE "psbt" (PSBT.ofBase64 both.psbt)
  let (_, tx) ← needM "finalize" (account.finalizeSpend full record.utxos (Real.ownedCoordinates record) height)
  check "finalized with one input" (tx.inputs.size == 1)
  -- A refusal on the Ledger reaches the user as that, and signs nothing.
  device.modify (·.setDecision .reject)
  let unsigned ← Real.createMultisigSpend phone.env phone.multisig id destination 40_000 2.0 false
  failsWith "a refusal on the Ledger" (Real.signMultisigSpendWithLedger phone.env phone.multisig true id unsigned.psbt)
    LedgerError.rejectedOnDevice.description
  failsWith "Ledger signing refuses Simple mode" (Real.signMultisigSpendWithLedger phone.env phone.multisig false id unsigned.psbt)
    Real.advancedModeOnlyText

def testBuilderMakesTwoOfThreeWithAnotherWinnowALedgerAndRecovery : IO Unit := do
  let phone ← phoneWith 0xA1
  let device ← simulator 0xB2
  phone.useLedger device
  let ms ← masters
  let otherWinnow ← keyExpression ms[2]!
  let (id, descriptor, _) ← phone.buildWithLedger "Family 2-of-3" [s!" {otherWinnow} "] (recovery := some (.fewerSigners 1 4320))
  let account ← needM "account" (MultisigAccount.parse descriptor signet)
  check "2 of 3 with recovery" (account.threshold == 2 && account.signers.size == 3 &&
    (account.recovery.map (·.blocks)) == some 4320 && (account.recovery.map (·.threshold)) == some 1)
  check "registered" ((← phone.record id).ledger.isSome && (← device.get).registeredNames == #["Family 2-of-3"])
  let otherKey ← needE "other account key" (ms[2]!.derived "m/86'/1'/0'")
  check "the other Winnow's key is a signer" (account.includes otherKey.neutered)
  check "one account" ((← phone.accounts).length == 1)
  let some ledger := (← phone.backend.multisigOverview).ledgers.head? | throw (IO.userError "no Ledger")
  failsWith "a name the Ledger cannot show"
    (phone.build "Family é" 2 [[← phone.keyExpression], [otherWinnow], ledger.keys]) Real.invalidNameText

def testStoreRefusesARegistrationForAnotherAccount : IO Unit := do
  let phone ← phoneWith 0xA1
  phone.useLedger (← simulator 0xB2)
  let (id, _, _) ← phone.buildWithLedger "Phone and Ledger"
  let record ← phone.record id
  let some registration := record.ledger | throw (IO.userError "no registration")
  let forged := { registration with policyID := zeros 32 0x11 }
  match ← (Real.setLedger phone.multisig id forged).toBaseIO with
  | .ok _ => check "a registration for another policy is not filed" false
  | .error _ => check "a registration for another policy is not filed" true
  check "the store keeps the real one" ((← phone.record id).ledger == some registration)
  check "validate refuses a tampered record"
    ((← (MultisigStore.validate #[{ record with ledger := some forged }] signet).run) matches .error _)
  check "validate accepts the record" ((← (MultisigStore.validate #[record] signet).run) matches .ok _)

def testBluetoothStatesStartFailOrWait : IO Unit := do
  check "poweredOn starts" (match Ledger.Bluetooth.readiness "poweredOn" with | some (.ok ()) => true | _ => false)
  for state in ["poweredOff", "unauthorized", "unsupported"] do
    check s!"{state} fails with a step the user can take" (match Ledger.Bluetooth.readiness state with
      | some (.error (.transport _)) => true | _ => false)
  check "resetting and unknown wait" ((Ledger.Bluetooth.readiness "resetting").isNone && (Ledger.Bluetooth.readiness "unknown").isNone)
  -- the app's transport over a shell answering `unsupported` (the simulator has no Bluetooth)
  let ask : Real.Ask := fun name _ => pure (Task.pure (if name == "ble.state" then
    Lean.Json.mkObj [("state", .str "unsupported")] else Lean.Json.mkObj [("ok", .bool false)]))
  match ← (Real.openLedger ask).toBaseIO with
  | .ok _ => check "no Bluetooth: opening fails" false
  | .error e => check "no Bluetooth: Swift's text" (toString e ==
      (LedgerError.transport "this device has no Bluetooth Low Energy").description) (toString e)

def testNotificationsReachOnlyTheStepInFlight : IO Unit := do
  let router : Ledger.Bluetooth.NotificationRouter := {}
  let mtu := ByteArray.mk #[0x08, 0, 0, 0, 1, 153]
  check "the frame-size reply while asking for it" (((router.receive mtu (some .frameSize)).2.map (·.toOption)) == some (some mtu))
  check "a reply frame is not a frame size" (router.receive (ByteArray.mk #[0x05, 0, 0, 0, 2, 0x90, 0x00]) (some .frameSize)).2.isNone
  check "nothing reaches a written step" (router.receive mtu (some .written)).2.isNone
  check "nothing reaches no step" (router.receive mtu none).2.isNone
  let reply := zeros 30 0x42
  let frames ← needE "frames" (Ledger.BluetoothFraming.frames reply 20)
  check "two frames" (frames.size == 2)
  let (r1, first) := router.receive frames[0]! (some .reply)
  check "the first frame completes nothing" first.isNone
  check "the second completes the reply" (((r1.receive frames[1]! (some .reply)).2.map (·.toOption)) == some (some reply))
  check "a frame without the APDU tag fails the reply" (match ((({} : Ledger.Bluetooth.NotificationRouter).receive
    (ByteArray.mk #[0x07, 0, 0]) (some .reply)).2) with | some (.error _) => true | _ => false)

def ledgerTests : List (String × IO Unit) :=
  [ ("testLedgerSigningIsAdvancedModeOnly", testLedgerSigningIsAdvancedModeOnly)
  , ("testPairVerifyAndSpendWithBothSigners", testPairVerifyAndSpendWithBothSigners)
  , ("testBuilderMakesTwoOfThreeWithAnotherWinnowALedgerAndRecovery", testBuilderMakesTwoOfThreeWithAnotherWinnowALedgerAndRecovery)
  , ("testStoreRefusesARegistrationForAnotherAccount", testStoreRefusesARegistrationForAnotherAccount)
  , ("testBluetoothStatesStartFailOrWait", testBluetoothStatesStartFailOrWait)
  , ("testNotificationsReachOnlyTheStepInFlight", testNotificationsReachOnlyTheStepInFlight) ]

/-! ## SignerRosterTests (upstream d2ca878) -/

def failsStarting {α} (name : String) (x : IO α) (prefix_ : String) : IO Unit := do
  match ← (x.toBaseIO) with
  | .ok _ => check name false "accepted"
  | .error e => check name ((toString e).startsWith prefix_) s!"got {e}"

def Phone.signers (p : Phone) : IO (List SignerInfo) := do return (← p.backend.multisigOverview).signers
def Phone.dir (p : Phone) : IO System.FilePath := do
  let some d := (← p.env.get).dir | throw (IO.userError "no directory")
  return System.FilePath.mk d
/-- `importWallet(bundleJSON:)` with the scene going to the background as soon as the import builds its
stack: the catch-up scan, which has no peer in this fixture, is not what these tests are about. -/
def Phone.importOffline (p : Phone) (json : String) : IO String := do
  let dir ← p.dir
  let _stopper ← IO.asTask do
    for _ in [0:600] do
      IO.sleep 50
      if (← p.env.get).stack.isSome then
        p.backend.stopNetworking
        return
  return (← p.backend.importBundle .signet dir.toString json).2

/-- `configureSigners()`: the file read again. -/
def Phone.reloadSigners (p : Phone) : IO Unit := do p.multisig.signers.configure signet (some (← p.dir))

def testPairedLedgerAndSavedKeysPersistAndRefuseDuplicates : IO Unit := do
  let phone ← phoneWith 0xA1
  let ms ← masters
  phone.useLedger (← simulator 0xB2)
  let ledgerID ← phone.backend.pairLedger true "Nano X"
  let some ledger := (← phone.signers).find? (·.id == ledgerID) | throw (IO.userError "no Ledger signer")
  check "paired: a Ledger with one key" (ledger.isLedger && ledger.keys.length == 1)
  check "its keys text is its fingerprint" (ledger.keysText == Descriptor.hex8 ms[1]!.fingerprint) ledger.keysText
  -- Bob's phone and Ledger, sent together, are one signer.
  let bobPhone ← keyExpression ms[2]!
  let bobLedger ← keyExpression (← master 0xD4)
  let bobID ← phone.backend.addSignerKeys true "Bob" s!" {bobPhone}\n{bobLedger} "
  let some bob := (← phone.signers).find? (·.id == bobID) | throw (IO.userError "no Bob")
  check "Bob's two keys" (bob.keys == [bobPhone, bobLedger] && !bob.isLedger)
  check "the list" ((← phone.signers).map (·.name) == ["Nano X", "Bob"])
  -- A key already held is refused, the Ledger's too; so are text that is no key and a mainnet key.
  failsWith "a key saved twice" (phone.backend.addSignerKeys true "Bob again" bobLedger) "That key is already saved as Bob."
  failsWith "the Ledger's key again" (phone.backend.addSignerKeys true "Me" ledger.keys[0]!) "That key is already saved as Nano X."
  for text in ["tpubnonsense", bobPhone.replace "tpub" "xpub", s!"sortedmulti_a(2,{bobPhone})"] do
    failsStarting s!"not a signer: {(text.take 20).toString}" (phone.backend.addSignerKeys true "Nobody" text)
      "The multisig descriptor is invalid:"
  check "still two" ((← phone.signers).length == 2)
  -- Renamed, written sealed, and read back from disk.
  phone.backend.renameSigner bobID "Bob and his Ledger"
  phone.reloadSigners
  let o ← phone.backend.multisigOverview
  check "read back: no notice" o.signerNotice.isNone
  check "read back: renamed" (o.signers.map (·.name) == ["Nano X", "Bob and his Ledger"])
  check "read back: Bob's keys" ((o.signers.getLast?.map (·.keys)) == some [bobPhone, bobLedger])
  let sealed ← IO.FS.readBinFile ((← phone.dir) / "signers.json")
  check "the file is sealed" (SealedStoreFile.isSealed sealed)
  -- An unsealed file put there by something else is refused, and the list stays empty.
  IO.FS.writeBinFile ((← phone.dir) / "signers.json") (unsealedPayloadOf sealed)
  phone.reloadSigners
  let o ← phone.backend.multisigOverview
  check "planted: a notice" o.signerNotice.isSome
  check "planted: nothing trusted" o.signers.isEmpty
  failsWith "a damaged list is not changed" (phone.backend.addSignerKeys true "Carol" bobPhone)
    "Winnow could not safely read its signers, so they cannot be changed until the file is readable again."

def testEveryBackupCarriesTheListAndAnImportMergesIt : IO Unit := do
  let phone ← phoneWith 0xA1
  let ms ← masters
  phone.useLedger (← simulator 0xB2)
  let ledgerID ← phone.backend.pairLedger true "Nano X"
  let bobID ← phone.backend.addSignerKeys true "Bob" (← keyExpression ms[2]!)
  let json ← phone.backend.exportBundle true
  let bundle ← needE "bundle" (ImportBundle.decode json)
  check "the export carries both" ((bundle.signers.map (·.toList.map (·.name))) == some ["Nano X", "Bob"])
  check "with the Ledger's fingerprint" ((bundle.signers.bind (·[0]?)).bind (·.masterFingerprint) == some ms[1]!.fingerprint)
  -- Restored on a phone that lost Bob and saved Carol since: Bob is back, Carol and the Ledger stay.
  phone.backend.removeSigner bobID
  let carolID ← phone.backend.addSignerKeys true "Carol" (← keyExpression (← master 0xE5))
  discard <| phone.importOffline json
  let signers ← phone.signers
  check "merged: the phone's own first, the bundle's added" (signers.map (·.id) == [ledgerID, carolID, bobID])
    s!"{signers.map (·.name)}"
  check "merged names" (signers.map (·.name) == ["Nano X", "Carol", "Bob"])
  -- A list the store refuses (a Ledger record without its own key) stops the import before anything.
  let fake : SignerRecord := { id := "fake", kind := .ledger, name := "Not a Ledger", keys := #[← keyExpression ms[2]!],
                               masterFingerprint := some ms[1]!.fingerprint, addedAt := 0 }
  failsWith "a refused list stops the import" (phone.importOffline ({ bundle with signers := some #[fake] }).serialized)
    "Invalid signer storage: a Ledger's record does not carry its own key"
  check "the list unchanged" ((← phone.signers).length == 3)

def testARestoredListJoinsThePhonesOwn : IO Unit := do
  let ms ← masters
  let keys ← memoryKeys
  let (store, _) ← SignerStore.configure keys none signet
  let bob ← keyExpression ms[2]!
  let (store, local_) ← need "add" (store.addKeys keys writeAtomically "Bob" #[bob] "local-bob" 0)
  let incoming : Array SignerRecord :=
    #[{ id := "other-bob", kind := .keys, name := "Bob elsewhere", keys := #[bob], addedAt := 0 },
      { id := "carol", kind := .keys, name := "Carol", keys := #[← keyExpression (← master 0xE5)], addedAt := 0 }]
  let merged ← need "plan" (store.planRestore incoming)
  check "the record here stays; the same key under another id is dropped; a new one joins"
    (merged.toList.map (·.name) == ["Bob", "Carol"])
  let store ← need "restore" (store.restore keys writeAtomically merged)
  check "restored ids" (store.records.toList.map (·.id) == [local_.id, "carol"])
  let fake : SignerRecord := { id := "fake", kind := .ledger, name := "Not a Ledger", keys := #[← keyExpression ms[1]!],
                               masterFingerprint := some ms[1]!.fingerprint, addedAt := 0 }
  refused "a Ledger record must carry its own key at the Ledger's path" (SignerStore.validateBackup #[fake] signet)
    "invalidState"

def testBuilderTakesMembersFromTheListAndAWholeAccountAsOne : IO Unit := do
  let phone ← phoneWith 0xA1
  let ms ← masters
  let nanoX ← simulator 0xB2
  phone.useLedger nanoX
  let ledgerID ← phone.backend.pairLedger true "Nano X"
  let o ← phone.backend.multisigOverview
  let some ledger := o.signers.find? (·.id == ledgerID) | throw (IO.userError "no Ledger")
  let phoneKey ← phone.keyExpression
  let bobID ← phone.backend.addSignerKeys true "Bob" s!"{← keyExpression ms[2]!} {← keyExpression (← master 0xD4)}"
  let carolMaster ← master 0xE5
  let carolID ← phone.backend.addSignerKeys true "Carol" (← keyExpression carolMaster)
  let signers ← phone.signers
  let some bob := signers.find? (·.id == bobID) | throw (IO.userError "no Bob")
  let some carol := signers.find? (·.id == carolID) | throw (IO.userError "no Carol")
  -- The household: this phone and its Ledger, 2-of-2, which the Ledger approves.
  let (householdID, householdD, reg) ← phone.backend.createMultisigAccount true "Household" 2
    [([phoneKey], none), (ledger.keys, none)] none
  check "the household is approved on the Ledger" (reg matches some (.ok "Nano X"))
  let household ← needM "household" (MultisigAccount.parse householdD signet)
  check "the household's preview" (previewText household == "2 of 2: any 2 of the 2 keys sign a spend.") (previewText household)
  check "the household's keys" (household.signerExpressions.toList.mergeSort (· ≤ ·) == ([phoneKey] ++ ledger.keys).mergeSort (· ≤ ·))
  -- The household's keys as one member of a 2-of-3 with Bob and Carol.
  let (nestedID, nestedD, reg) ← phone.backend.createMultisigAccount true "Three households" 2
    [(household.signerExpressions.toList, none), (bob.keys, none), (carol.keys, none)] none
  let account ← needM "nested" (MultisigAccount.parse nestedD signet)
  check "2 of 3 members" (account.policySummary == "2 of 3 members") account.policySummary
  check "member sizes" ((account.members.map (·.groups.toList.map (·.size) |>.mergeSort (· ≤ ·))) == some [1, 2, 2])
  check "the nested preview" (previewText account ==
    "2 of 3 members: 3 ways to spend, each needing every key it lists, up to 4 keys. A member short of the keys it needs cannot help.")
    (previewText account)
  check "registered on the Ledger" (reg matches some (.ok "Nano X"))
  check "the Ledger saw both names" ((← nanoX.get).registeredNames == #["Household", "Three households"])
  let registered ← phone.record nestedID
  check "the registration is the Ledger's" ((registered.ledger.map (·.masterFingerprint)) == some ms[1]!.fingerprint)
  let names := Real.signerNames (← phone.multisig.signers.all) registered signet
  check "names: the Ledger" (names.lookup ms[1]!.fingerprint == some "Nano X")
  check "names: Bob" (names.lookup ms[2]!.fingerprint == some "Bob")
  check "names: Carol" (names.lookup carolMaster.fingerprint == some "Carol")
  -- A second Ledger of this phone in the same account is refused.
  phone.useLedger (← simulator 0xE6)
  let nanoSID ← phone.backend.pairLedger true "Nano S"
  let some nanoS := (← phone.signers).find? (·.id == nanoSID) | throw (IO.userError "no Nano S")
  check "two Ledgers listed" ((← phone.backend.multisigOverview).ledgers.map (·.name) == ["Nano X", "Nano S"])
  failsWith "two of this phone's Ledgers" (phone.build "Two Ledgers" 2 [[phoneKey], ledger.keys, nanoS.keys])
    Real.oneLedgerPerAccountText
  failsWith "a Ledger account wants a name it can show" (phone.build "Ménage à trois" 2 [[phoneKey], ledger.keys, carol.keys])
    Real.invalidNameText
  check "two accounts" ((← phone.accounts).length == 2)
  check "the household" (householdID != nestedID)

/-! ## NestedMultisigFlowTests (upstream d2ca878) -/

def destinationOf (m : Keys.HDKey) (index : UInt32) : IO String := do
  let d ← needE "destination descriptor" (Descriptor.parse s!"tr({← keyExpression m})")
  return (← needE "derived" (d.derived index signet))[0]!.address

def completePaths (s : MultisigScreen) : List (Bool × Nat × Nat) := s.signatures.filter fun (_, a, t) => a ≥ t

def testTwoPhonesWithLedgersAndAThirdMember : IO Unit := do
  let phoneA ← phoneWith 0xA1
  let phoneB ← phoneWith 0xC3
  let ledgerA ← simulator 0xB2
  let ledgerB ← simulator 0xD5
  phoneA.useLedger ledgerA
  phoneB.useLedger ledgerB
  let third ← master 0xD4
  let pairedA ← phoneA.backend.pairLedger true "Ledger A"
  let pairedB ← phoneB.backend.pairLedger true "Ledger B"
  let some ledgerAInfo := (← phoneA.signers).find? (·.id == pairedA) | throw (IO.userError "no Ledger A")
  let some ledgerBInfo := (← phoneB.signers).find? (·.id == pairedB) | throw (IO.userError "no Ledger B")
  let shareB := (← phoneB.keyExpression) ++ "\n" ++ ledgerBInfo.keys.headD ""
  let savedB ← phoneA.backend.addSignerKeys true "Household B" shareB
  let some savedBInfo := (← phoneA.signers).find? (·.id == savedB) | throw (IO.userError "no B")
  check "B's share is two keys" (savedBInfo.keys.length == 2)
  let savedThird ← phoneA.backend.addSignerKeys true "Carol" (← keyExpression third)
  let some thirdInfo := (← phoneA.signers).find? (·.id == savedThird) | throw (IO.userError "no Carol")
  let (id, descriptor, reg) ← phoneA.backend.createMultisigAccount true "Three households" 2
    [((← phoneA.keyExpression) :: ledgerAInfo.keys, none), (savedBInfo.keys, none), (thirdInfo.keys, none)] none
  let account ← needM "account" (MultisigAccount.parse descriptor signet)
  check "nested" account.isNested
  check "2 of 3 members" (account.policySummary == "2 of 3 members")
  check "Ledger A registered it" (reg matches some (.ok "Ledger A"))
  check "Ledger A saw the name" ((← ledgerA.get).registeredNames == #["Three households"])
  check "phone A's record has the registration" (← phoneA.record id).ledger.isSome
  let some infoA := (← phoneA.accounts).find? (·.id == id) | throw (IO.userError "no info")
  let lines := infoA.memberLines
  let has (needle : String) (line : String) := (line.splitOn needle).length > 1
  check "names: this phone with Ledger A" (lines.any fun l => has "(this phone)" l && has "(Ledger A)" l) s!"{lines}"
  check "names: Household B" (lines.any (has "(Household B)")) s!"{lines}"
  check "names: Carol" (lines.any (has "(Carol)")) s!"{lines}"
  check "the members header" (infoA.membersHeader == some "Members · any 2 of 3")
  -- Phone B joins with the descriptor; its own paired Ledger registers it.
  let (joined, regB) ← phoneB.backend.addMultisigAccount true "Three households" descriptor
  check "B joined the same account" (joined == id)
  check "Ledger B registered it" (regB matches some (.ok "Ledger B"))
  check "Ledger B saw the name" ((← ledgerB.get).registeredNames == #["Three households"])
  check "B's registration is Ledger B's" (((← phoneB.record id).ledger.map (·.masterFingerprint)) == some (← master 0xD5).fingerprint)
  -- The same coin reaches both phones.
  let height := (← phoneA.record id).createdAtHeight + 1
  let funding := spend #[⟨zeros 32 0x36, 0⟩] #[{ value := 80_000, scriptPubKey := ← spk account 0 }]
  for p in [phoneA, phoneB] do
    discard <| p.multisig.applyMatch (fakeMatch height #[coinbaseAt height, funding]) signet
  check "funded" ((← phoneA.record id).balance == 80_000)
  -- Phone A creates the spend: three groups could finish it, none has.
  let destination ← destinationOf third 1
  let created ← Real.createMultisigSpend phoneA.env phoneA.multisig id destination 50_000 2.0 false
  let screen ← screenOf created
  check "three paths" (screen.signatures.length == 3)
  check "the group titles" (screen.signatureTitles.map (·.1) == ["Group 1 signatures", "Group 2 signatures", "Group 3 signatures"])
  check "both devices wanted" (screen.progress == { phoneHolds := true, phoneUnsigned := true, ledgerHolds := true, ledgerUnsigned := true })
  -- Household A signs with both devices: one member, nothing finishes.
  let signed ← Real.signMultisigSpend phoneA.env phoneA.multisig id created.psbt
  let signed ← Real.signMultisigSpendWithLedger phoneA.env phoneA.multisig true id signed.psbt
  let screen ← screenOf signed
  check "one member is not enough" (!(screen.progress.complete || screen.progress.phoneUnsigned || screen.progress.ledgerUnsigned))
  check "share it" (screen.progress.nextStep.startsWith "Share the PSBT")
  -- Household B signs its copy with both devices; A combines it.
  let copy ← Real.signMultisigSpend phoneB.env phoneB.multisig id signed.psbt
  let copy ← Real.signMultisigSpendWithLedger phoneB.env phoneB.multisig true id copy.psbt
  let combined ← Real.addPastedPSBT phoneA.env phoneA.multisig id (some signed.psbt) copy.psbt
  let screen ← screenOf combined
  check "two whole members: complete" screen.progress.complete
  check "exactly one leaf finishes, of four keys" (completePaths screen == [(false, 4, 4)]) s!"{screen.signatures}"
  let record ← phoneA.record id
  let full ← needE "psbt" (PSBT.ofBase64 combined.psbt)
  let (_, tx) ← needM "finalize" (account.finalizeSpend full record.utxos (Real.ownedCoordinates record) height)
  check "four signatures, the leaf and its control block" (tx.inputs[0]!.witness.size == 6)

def testAThresholdAccountAsOneMember : IO Unit := do
  let phone ← phoneWith 0xA1
  let ms ← masters
  let ledger ← simulator 0xD5
  phone.useLedger ledger
  let nanoXID ← phone.backend.pairLedger true "Nano X"
  let bobID ← phone.backend.addSignerKeys true "Bob" (← keyExpression ms[1]!)
  let carolID ← phone.backend.addSignerKeys true "Carol" (← keyExpression ms[2]!)
  let daveMaster ← master 0xE5
  let daveID ← phone.backend.addSignerKeys true "Dave" (← keyExpression daveMaster)
  let signers ← phone.signers
  let keysOf (id : String) : List String := ((signers.find? (·.id == id)).map (·.keys)).getD []
  let phoneKey ← phone.keyExpression
  -- The family: this phone, Bob and Carol, any two.
  let (familyID, _) ← phone.build "Family" 2 [[phoneKey], keysOf bobID, keysOf carolID]
  let some family := (← phone.accounts).find? (·.id == familyID) | throw (IO.userError "no family")
  check "picker: eligible" (pickerAccountText family true == "2 of 3: any 2 of its 3 keys") (pickerAccountText family true)
  check "picker: not into a member" (pickerAccountText family false == "2 of 3: a member of its own only")
  check "picker: into a member it is not eligible" (!pickerAccountEligible family false && pickerAccountEligible family true)
  let member : BuildMember :=
    { keys := family.signerExpressions.map fun k => { key := k, label := if k == phoneKey then phoneLabel else "Family" },
      name := some "Family", threshold := some 2 }
  check "member title" (member.title == "Family 2-of-3") member.title
  check "member caption" (member.caption == some "any 2 of its 3 keys")
  check "a threshold member" member.isThreshold
  -- The estate: the family, the Ledger and Dave, any two members.
  let (estateID, estateD, reg) ← phone.backend.createMultisigAccount true "Estate" 2
    [member.plan, (keysOf nanoXID, none), (keysOf daveID, none)] none
  let account ← needM "estate" (MultisigAccount.parse estateD signet)
  check "nested, seven leaves" (account.isNested && account.signersLeaves.size == 7)
  check "the summary" (account.policySummary == "2 of 3 members, one of them 2 of 3") account.policySummary
  check "the preview" (previewText account ==
    "2 of 3 members, one of them 2 of 3: 7 ways to spend, each needing every key it lists, up to 3 keys. A member short of the keys it needs cannot help.")
  let some estate := (← phone.accounts).find? (·.id == estateID) | throw (IO.userError "no estate")
  check "a nested account cannot be one member yet"
    (pickerAccountText estate false == "2 of 3 members, one of them 2 of 3: cannot be one member yet")
  check "member thresholds" ((account.members.map (·.thresholds.toList.mergeSort (· ≤ ·))) == some [1, 1, 2])
  let has (needle : String) (line : String) := (line.splitOn needle).length > 1
  let lines := estate.memberLines
  check "the family line" (lines.any fun l => l.startsWith "any 2 of: " && has "(this phone)" l && has "(Bob)" l && has "(Carol)" l)
    s!"{lines}"
  check "the Ledger line" (lines.any fun l => has "(Nano X)" l && !l.startsWith "any") s!"{lines}"
  check "the Dave line" (lines.any (has "(Dave)")) s!"{lines}"
  check "registered" (reg matches some (.ok "Nano X"))
  check "the Ledger saw the estate" ((← ledger.get).registeredNames == #["Estate"])
  -- A coin, and a spend: the phone's family key and the Ledger are one whole member; Bob completes the family.
  let height := (← phone.record estateID).createdAtHeight + 1
  let funding := spend #[⟨zeros 32 0x37, 0⟩] #[{ value := 80_000, scriptPubKey := ← spk account 0 }]
  discard <| phone.multisig.applyMatch (fakeMatch height #[coinbaseAt height, funding]) signet
  let record ← phone.record estateID
  check "funded" (record.balance == 80_000)
  let owned := Real.ownedCoordinates record
  let tip ← Real.chainTip phone.env
  let destination ← destinationOf daveMaster 1
  let created ← Real.createMultisigSpend phone.env phone.multisig estateID destination 50_000 2.0 false
  check "seven paths" ((← screenOf created).signatures.length == 7)
  let signed ← Real.signMultisigSpend phone.env phone.multisig estateID created.psbt
  let signed ← Real.signMultisigSpendWithLedger phone.env phone.multisig true estateID signed.psbt
  let screen ← screenOf signed
  check "not yet" (!(screen.progress.complete || screen.progress.phoneUnsigned || screen.progress.ledgerUnsigned))
  let psbt ← needE "psbt" (PSBT.ofBase64 signed.psbt)
  let psbt ← needM "Bob signs" (account.sign psbt ms[1]! record.utxos owned tip (zeros 32))
  let shown ← Real.reviewMultisigPSBT phone.env phone.multisig estateID psbt.base64
  let screen ← screenOf shown
  check "Bob completes the family: one leaf of three keys" (screen.progress.complete && completePaths screen == [(false, 3, 3)])
    s!"{screen.signatures}"
  let (_, tx) ← needM "finalize" (account.finalizeSpend psbt record.utxos owned tip)
  check "three signatures, the leaf and its control block" (tx.inputs[0]!.witness.size == 5)
  -- This phone and Dave: one family key and one whole member, nothing; Carol completes the family.
  let other ← Real.createMultisigSpend phone.env phone.multisig estateID destination 50_000 2.0 false
  let other ← Real.signMultisigSpend phone.env phone.multisig estateID other.psbt
  let o ← needE "psbt" (PSBT.ofBase64 other.psbt)
  let o ← needM "Dave signs" (account.sign o daveMaster record.utxos owned tip (zeros 32))
  check "the phone and Dave are not enough"
    (!((← screenOf (← Real.reviewMultisigPSBT phone.env phone.multisig estateID o.base64)).progress.complete))
  let o ← needM "Carol signs" (account.sign o ms[2]! record.utxos owned tip (zeros 32))
  let screen ← screenOf (← Real.reviewMultisigPSBT phone.env phone.multisig estateID o.base64)
  check "Carol completes the family" (screen.progress.complete && (completePaths screen).length == 1)

def testPairingSavingAndRegisteringAreAdvancedModeOnly : IO Unit := do
  let phone ← phoneWith 0xA1
  phone.useLedger (← simulator 0xB2)
  failsWith "pairing in Simple mode" (phone.backend.pairLedger false "Nano X") Real.advancedModeOnlyText
  failsWith "saving keys in Simple mode" (phone.backend.addSignerKeys false "Bob" (← keyExpression (← masters)[2]!))
    Real.advancedModeOnlyText
  failsWith "registering in Simple mode" (phone.backend.registerLedger false "x") Real.advancedModeOnlyText
  check "no signers" (← phone.signers).isEmpty

def nestedTests : List (String × IO Unit) :=
  [ ("testTwoPhonesWithLedgersAndAThirdMember", testTwoPhonesWithLedgersAndAThirdMember)
  , ("testAThresholdAccountAsOneMember", testAThresholdAccountAsOneMember)
  , ("testPairingSavingAndRegisteringAreAdvancedModeOnly", testPairingSavingAndRegisteringAreAdvancedModeOnly) ]

/-- The signer list is not a wallet's: deleting the wallet keeps `signers.json`, and the list reads back. -/
def testTheSignerListSurvivesDeletingTheWallet : IO Unit := do
  let phone ← phoneWith 0xA1
  let dir ← phone.dir
  discard <| phone.backend.addSignerKeys true "Bob" (← keyExpression (← masters)[2]!)
  phone.backend.deleteWallet
  check "signers.json stays" (← (dir / "signers.json").pathExists)
  let o ← phone.backend.multisigOverview
  check "the list reads back after the deletion" (o.signers.map (·.name) == ["Bob"] && o.signerNotice.isNone)

def signerTests : List (String × IO Unit) :=
  [ ("testPairedLedgerAndSavedKeysPersistAndRefuseDuplicates", testPairedLedgerAndSavedKeysPersistAndRefuseDuplicates)
  , ("testEveryBackupCarriesTheListAndAnImportMergesIt", testEveryBackupCarriesTheListAndAnImportMergesIt)
  , ("testARestoredListJoinsThePhonesOwn", testARestoredListJoinsThePhonesOwn)
  , ("testBuilderTakesMembersFromTheListAndAWholeAccountAsOne", testBuilderTakesMembersFromTheListAndAWholeAccountAsOne)
  , ("testTheSignerListSurvivesDeletingTheWallet", testTheSignerListSurvivesDeletingTheWallet) ]

/-! ## MultisigAccountFlowTests: one wallet (upstream #259) -/

/-- Two phones sharing a 2-of-2, the account funded by one block on both; this phone has a stack, so a
broadcast queues with its broadcaster (no peer answers in this fixture). -/
structure TwoPhones where
  phone : Phone
  other : Phone
  id : String
  account : MultisigAccount
  funding : Transaction
  height : UInt32

initialize stackedPhones : IO.Ref (Array Phone) ← IO.mkRef #[]

def twoPhones : IO TwoPhones := do
  let phone ← phoneWith 0xA1
  let other ← phoneWith 0xC3
  Real.buildStackIfNeeded phone.env
  stackedPhones.modify (·.push phone)
  check "this phone has a stack" (← phone.env.get).stack.isSome
  let (id, d) ← phone.build "Two phones" 2 [[← phone.keyExpression], [← other.keyExpression]]
  discard <| other.join "Two phones" d
  let account ← needM "account" (MultisigAccount.parse d signet)
  let height := (← phone.record id).createdAtHeight + 1
  let funding := spend #[⟨zeros 32 0x45, 0⟩] #[{ value := 60_000, scriptPubKey := ← spk account 0 }]
  for p in [phone, other] do
    discard <| p.multisig.applyMatch (block height #[funding]) signet
  return { phone, other, id, account, funding, height }

def Phone.status (p : Phone) : IO Status := do return (← p.backend.snapshot).1
def Phone.info (p : Phone) (id : String) : IO MultisigInfo := do
  let some i := (← p.accounts).find? (·.id == id) | throw (IO.userError s!"no account {id}")
  return i

def accountDestination (index : UInt32 := 0) : IO String := do destinationOf (← masters)[1]! index

def accountInputs (id destination : String) (amount : Nat) : SendInputs :=
  { destination, amount := toString amount, network := .signet, accountID := some id }

/-- The other phone signs this phone's draft and this phone takes the signatures back, the way the PSBT
text travels between signers. -/
def collectOtherSignature (t : TwoPhones) : IO Unit := do
  let some d := (← t.phone.record t.id).draft | throw (IO.userError "no draft")
  t.other.backend.adoptDraft t.id d.psbtBase64
  t.other.backend.signDraft t.id
  let some theirs := (← t.other.record t.id).draft | throw (IO.userError "no draft on the other phone")
  t.phone.backend.adoptDraft t.id theirs.psbtBase64

def isV0 (text : String) : Bool :=
  match PSBT.ofBase64 text with
  | .ok p => p.base64V0.toOption == some text
  | .error _ => false

/-- Send, From: the account. The review is the PSBT this phone built; "Sign and continue" files it as the
draft (BIP174 v0), which survives a reload and shows in Transactions; the other phone signs; the broadcast
lands in both phones' lists named with the account, confirms in place, and a reorg re-pends it. -/
def testSendTabSpendsFromAnAccountAcrossTwoPhones : IO Unit := do
  let t ← twoPhones
  let phone := t.phone
  let s ← phone.status
  check "one balance: the account's" (s.accountsBalance == 60_000 && s.balance == 0)
  check "one row: the funding" (s.payments.map (·.item.txid) == [Winnow.displayHex t.funding.txid])
  check "named with the account" ((s.payments.head?.map (·.source)) == some (.account "Two phones"))
  check "received at its height" ((s.payments.head?.map fun r => (r.item.received, r.item.height)) == some (60_000, t.height.toNat))
  let destination ← accountDestination
  let inputs := accountInputs t.id destination 25_000
  let preview ← phone.backend.previewSend inputs
  check "the review names the account" ((preview.account.map fun a => (a.name, a.threshold, a.signerCount)) == some ("Two phones", 2, 2))
  check "the review's amounts" (preview.amount == 25_000 && preview.inputCount == 1 && preview.change == some (60_000 - 25_000 - preview.fee))
  failsWith "no silent payment code from an account" (phone.backend.previewSend (accountInputs t.id "tsp1qqnonsense" 1_000))
    Real.silentPaymentUnsupportedText
  failsWith "Sign and continue is Advanced mode's" (phone.backend.signAndDraft false inputs preview) Real.advancedModeOnlyText
  failsWith "a review for other inputs does not sign" (phone.backend.signAndDraft true { inputs with amount := "25001" } preview)
    (Real.AppError.sendReviewChanged).text
  discard <| phone.backend.signAndDraft true inputs preview
  let record ← phone.record t.id
  let some d := record.draft | throw (IO.userError "no draft")
  check "the draft is BIP174 v0 (fixed upstream bug 1)" (isV0 d.psbtBase64)
  let info ← phone.info t.id
  check "one signature: this phone's" ((info.draft.bind (·.screen)).map (·.signatures) == some [(false, 1, 2)])
  check "signed here" ((info.draft.bind (·.screen)).any (·.progress.signedHere))
  check "the share text is the draft's v0" ((info.draft.map (·.psbt)) == some d.psbtBase64)
  let s ← phone.status
  let some row := s.payments.head? | throw (IO.userError "no rows")
  check "the draft row on top" (row.isDraft && row.source == .draft "Two phones" "1 of 2") s!"{repr row.source}"
  check "the draft row's txid" (some row.item.txid == ((d.txid.toOption).map Winnow.displayHex))
  check "the draft row's amounts" (row.item.spent == 60_000 && row.item.received == (60_000 - 25_000 - preview.fee : Nat) &&
    row.item.fee == some (preview.fee : Int))
  check "the draft row's recipient" ((paymentRecipients {} row.item).map (·.amount) == [25_000])
  phone.multisig.host.configure signet (some (← phone.dir))
  check "the draft survives a reload" ((← phone.record t.id).draft == some d)
  failsWith "one draft per account" (phone.backend.previewSend (accountInputs t.id destination 1_000)) Real.draftInProgressText
  -- Another payment's PSBT cannot be combined into the draft.
  let different ← Real.createMultisigSpend t.other.env t.other.multisig t.id (← accountDestination 1) 1_000 1.0 false
  failsWith "a different payment is not combined" (phone.backend.adoptDraft t.id different.psbt) Real.draftMismatchText
  collectOtherSignature t
  check "complete" ((((← phone.info t.id).draft.bind (·.screen)).map (·.progress.complete)) == some true)
  let txid ← phone.backend.broadcastDraft t.id
  check "the draft's txid went out" (some txid == ((d.txid.toOption).map Winnow.displayHex))
  let record ← phone.record t.id
  check "the draft retired, the bytes kept" (record.draft.isNone && record.inFlight.map (Winnow.displayHex ·.txid) == #[txid])
  let s ← phone.status
  let some pending := s.payments.head? | throw (IO.userError "no rows")
  check "pending, named with the account, its exact fee" (pending.source == .account "Two phones" && pending.item.height == 0 &&
    pending.item.fee == some (preview.fee : Int))
  check "the balance follows" (s.accountsBalance == (60_000 - 25_000 - preview.fee : Nat))
  -- It confirms on both phones: in place here, as the account's spend there.
  let some spendTx := record.inFlight[0]?.bind (·.transaction.toOption) | throw (IO.userError "no bytes")
  for p in [phone, t.other] do
    discard <| p.multisig.applyMatch (block (t.height + 1) #[spendTx]) signet
  let s ← phone.status
  check "two rows, newest first" (s.payments.map (·.item.txid) == [txid, Winnow.displayHex t.funding.txid])
  check "confirmed in place" ((s.payments.head?.map (·.item.height)) == some (t.height + 1).toNat)
  let so ← t.other.status
  check "on the other phone: the account's spend" ((so.payments.head?.map fun r => (r.source, r.item.spent)) ==
    some (.account "Two phones", 60_000))
  check "its draft went with the coin" (← t.other.record t.id).draft.isNone
  -- A reorg below the spend puts it back in flight, bytes still kept.
  phone.multisig.rollBack t.height
  let s ← phone.status
  check "re-pended" ((s.payments.head?.map (·.item.height)) == some 0)
  check "bytes still kept" ((← phone.record t.id).inFlight.map (Winnow.displayHex ·.txid) == #[txid])

/-- A payment between the wallet and one of its accounts is one row. -/
def testATransferBetweenTheWalletAndAnAccountIsOneRow : IO Unit := do
  let t ← twoPhones
  let phone := t.phone
  let some w := (← phone.env.get).wallet | throw (IO.userError "no wallet")
  let walletScript ← match ← (w.scriptPubKey .receive 0).run with
    | .ok sc => pure sc | .error _ => throw (IO.userError "script")
  let walletFunding := spend #[⟨zeros 32 0x46, 0⟩] #[{ value := 30_000, scriptPubKey := walletScript }]
  discard <| phone.env.walletOp (w.apply (block (t.height + 1) #[walletFunding]))
  let change ← match ← (w.scriptPubKey .change 0).run with
    | .ok sc => pure sc | .error _ => throw (IO.userError "script")
  let transfer := spend #[⟨walletFunding.txid, 0⟩]
    #[{ value := 20_000, scriptPubKey := ← spk t.account 1 }, { value := 9_500, scriptPubKey := change }]
  let m := block (t.height + 2) #[transfer]
  discard <| phone.env.walletOp (w.apply m)
  discard <| phone.multisig.applyMatch m signet
  let s ← phone.status
  check "balances" (s.balance == 9_500 && s.accountsBalance == 80_000) s!"{s.balance} {s.accountsBalance}"
  check "three rows" (s.payments.map (·.item.txid) ==
    [Winnow.displayHex transfer.txid, Winnow.displayHex walletFunding.txid, Winnow.displayHex t.funding.txid])
  let some moved := s.payments.head? | throw (IO.userError "no rows")
  check "one transfer row" (moved.source == .transfer "Wallet" "Two phones" 20_000) s!"{repr moved.source}"
  check "carrying the wallet's entry" (moved.accountID.isNone && moved.item.spent == 30_000 && moved.item.fee == some 500)
  check "the payment screen's row" ((s.displayedPayment? (Winnow.displayHex transfer.txid)).map (·.source) == some moved.source)

/-- A backup carries a spend no block has taken, with its bytes, so a restored phone can announce it again;
given up on, its coins are the account's again. -/
def testAnInFlightAccountSpendSurvivesABackupAndCanBeRebroadcastOrGivenUp : IO Unit := do
  let t ← twoPhones
  let phone := t.phone
  let inputs := accountInputs t.id (← accountDestination) 25_000
  let preview ← phone.backend.previewSend inputs
  discard <| phone.backend.signAndDraft true inputs preview
  collectOtherSignature t
  let txid ← phone.backend.broadcastDraft t.id
  let json ← phone.backend.exportBundle false
  let bundle ← needE "bundle" (ImportBundle.decode json)
  let some carried := bundle.vaults.bind (·[0]?) | throw (IO.userError "no account in the backup")
  check "the backup carries the spend in flight" (carried.inFlight.map (Winnow.displayHex ·.txid) == #[txid])
  check "as pending in its history" (((carried.history.find? (Winnow.displayHex ·.txid == txid)).map (·.height)) == some 0)
  check "with bytes that are the spend" ((carried.inFlight[0]?.bind (·.transaction.toOption)).map (Winnow.displayHex ·.txid) == some txid)
  phone.backend.rebroadcastSpend t.id txid
  phone.backend.abandonSpend t.id txid
  let record ← phone.record t.id
  check "given up: nothing in flight, the coin back" (record.inFlight.isEmpty && record.balance == 60_000)
  let s ← phone.status
  check "given up: the balance and the list" (s.accountsBalance == 60_000 && s.payments.map (·.item.txid) == [Winnow.displayHex t.funding.txid])
  failsWith "a spend given up on is not announced" (phone.backend.rebroadcastSpend t.id txid) Real.notInFlightText

/-- Fixed upstream bug 3 through the app's hook: a block confirming the draft's own transaction, broadcast by
the co-signer, advances the paid person's address index here. -/
def testACoSignersBroadcastAdvancesThePaidPersonsIndex : IO Unit := do
  let t ← twoPhones
  let phone := t.phone
  let inputs := accountInputs t.id (← accountDestination) 25_000
  let preview ← phone.backend.previewSend inputs
  discard <| phone.backend.signAndDraft true inputs preview
  -- the draft pays a person at index 4 (as a Send to a saved person files it)
  let some d := (← phone.record t.id).draft | throw (IO.userError "no draft")
  Real.fileDraft phone.multisig t.id (some { d with personID := some "bob", paymentIndex := some 4 })
  collectOtherSignature t
  -- the other phone finalizes and broadcasts; its block reaches this phone
  let some theirs := (← t.phone.record t.id).draft | throw (IO.userError "no draft")
  let full ← needE "psbt" (PSBT.ofBase64 theirs.psbtBase64)
  let record ← phone.record t.id
  let (_, tx) ← needM "finalize" (t.account.finalizeSpend full record.utxos (Real.ownedCoordinates record) t.height)
  let advanced ← IO.mkRef (#[] : Array (String × UInt32))
  discard <| phone.multisig.applyMatchPaying (fun p i => advanced.modify (·.push (p, i))) (block (t.height + 1) #[tx]) signet
  check "Bob's index moves past 4 although this phone never broadcast" ((← advanced.get) == #[("bob", 4)])
  check "the draft went with its coin" (← phone.record t.id).draft.isNone

/-- The phones a test built a stack for are stopped when it ends (their tasks would keep the process up). -/
def withStacksStopped (t : IO Unit) : IO Unit := do
  try t finally
    for p in ← stackedPhones.get do p.backend.stopNetworking
    stackedPhones.set #[]

def oneWalletTests : List (String × IO Unit) :=
  [ ("testSendTabSpendsFromAnAccountAcrossTwoPhones", withStacksStopped testSendTabSpendsFromAnAccountAcrossTwoPhones)
  , ("testATransferBetweenTheWalletAndAnAccountIsOneRow", withStacksStopped testATransferBetweenTheWalletAndAnAccountIsOneRow)
  , ("testAnInFlightAccountSpendSurvivesABackupAndCanBeRebroadcastOrGivenUp",
      withStacksStopped testAnInFlightAccountSpendSurvivesABackupAndCanBeRebroadcastOrGivenUp)
  , ("testACoSignersBroadcastAdvancesThePaidPersonsIndex", withStacksStopped testACoSignersBroadcastAdvancesThePaidPersonsIndex) ]

/-! ## HistoryDisplayTests, SendReviewBindingTests, the draft row's leaf (pure) -/

def row (id : UInt8) (height : Nat) (received spent : Int) : HistoryItem :=
  { txid := Winnow.displayHex (zeros 32 id), height, received, spent, fee := none }

/-- The one list: wallet rows, account rows named, a transaction in both histories folded into one transfer
row, drafts on top, newest first. -/
def testPaymentsMergeWalletAndAccountRowsAndFoldTransfers : IO Unit := do
  let walletReceive := row 1 100 10_000 0
  let toAccount := row 2 105 4_000 10_000
  let accountSide := row 2 105 5_000 0
  let fromAccount := row 3 110 0 5_000
  let walletSide := row 3 110 4_500 0
  let bothSpent := row 4 111 0 1_000
  let bothSpentAccount := row 4 111 0 2_000
  let accountPending := row 5 0 0 3_000
  let draft : DisplayedPayment := { item := row 9 0 0 500, source := .draft "Household" "1 of 2", accountID := some "acct" }
  let rows := payments [walletReceive, toAccount, walletSide, bothSpent]
    [("acct", "Household", [accountSide, fromAccount, bothSpentAccount, accountPending])] [draft]
  check "order" (rows.map (·.item.txid) == [draft.item.txid, accountPending.txid, bothSpent.txid, bothSpentAccount.txid,
    fromAccount.txid, toAccount.txid, walletReceive.txid]) s!"{rows.map (·.item.txid.take 2)}"
  check "sources" (rows.map (·.source) == [.draft "Household" "1 of 2", .account "Household", .wallet, .account "Household",
    .transfer "Household" "Wallet" 4_500, .transfer "Wallet" "Household" 5_000, .wallet]) s!"{repr (rows.map (·.source))}"
  check "the transfer row carries the spender's entry" ((rows[4]?.bind (·.accountID)) == some "acct" &&
    (rows[5]?.bind (·.accountID)).isNone && (rows[5]?.map (·.item.spent)) == some 10_000)
  check "account names" (rows.map (·.accountName) ==
    [some "Household", some "Household", none, some "Household", some "Household", some "Household", none])

def testAReviewForTheWalletNeverSignsForAnAccount : IO Unit := do
  let baseline : SendInputs := { destination := "tb1p-destination", amount := "1000", network := .signet, walletID := some "w" }
  check "a review made for the wallet never signs for an account" (baseline != { baseline with accountID := some "household" })
  check "the same inputs are the same review" (baseline == { baseline with accountID := none })

/-- Fixed upstream bug 2: the leaf a draft row shows is chosen by signature counts as numbers. -/
def testTheDraftRowShowsTheLeafClosestToFinishing : IO Unit := do
  check "2 of 3 over an untouched 0 of 12 (upstream picked the longer text)" (bestLeafSignatures [(0, 12), (2, 3)] == some (2, 3))
  check "fewest further signatures" (bestLeafSignatures [(1, 3), (1, 2)] == some (1, 2))
  check "a tie: the most approvals" (bestLeafSignatures [(0, 1), (2, 3)] == some (2, 3))
  check "a full tie: the first path" (bestLeafSignatures [(1, 2), (1, 2)] == some (1, 2))
  check "complete beats incomplete" (bestLeafSignatures [(3, 4), (2, 2)] == some (2, 2))
  check "no path" (bestLeafSignatures [] == none)


/-! ## Simple mode, by taking away -/

def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The rendered tree as the shell receives it. -/
def rendered (m : Model) : String := (LeanNative.Html.toWire (view m)).toJson.compress

/-- A phone with a multisig account holding a draft, its rows in the one list, a paired Ledger and saved keys. -/
def modelWithAccounts (advanced : Bool) : Model :=
  let draftItem : HistoryItem := { txid := "dd", height := 0, received := 30_000, spent := 60_000, fee := some 500 }
  let accountItem : HistoryItem := { txid := "aa", height := 120, received := 60_000, spent := 0, fee := none }
  let walletItem : HistoryItem := { txid := "ww", height := 110, received := 10_000, spent := 0, fee := none }
  let account : MultisigInfo :=
    { id := "acct", name := "Household", descriptor := "tr(…)", balance := 60_000, policy := some "2 of 2",
      threshold := 2, signerCount := 2, needsLedgerRegistration := true,
      draft := some { psbt := "cHNidP8BAA", txid := "dd", signatures := "1 of 2" } }
  { stage := .ready, settings := { network := .signet, advancedMode := advanced }, walletID := some "w",
    status := { balance := 10_000, accountsBalance := 60_000, history := [walletItem],
                payments := [{ item := draftItem, source := .draft "Household" "1 of 2", accountID := some "acct" },
                             { item := accountItem, source := .account "Household", accountID := some "acct" },
                             { item := walletItem, source := .wallet }] },
    multisig := { accounts := [account], keyExpression := some "[deadbeef/86'/1'/0']tpubXYZ/<0;1>/*",
                  signers := [{ id := "l", isLedger := true, name := "Nano X", keys := ["k"], keysText := "5992698d" },
                              { id := "b", isLedger := false, name := "Bob", keys := ["k2"], keysText := "1a2b3c4d" }] } }

/-- The user's rule for Simple mode: Ledger, Signers, multisig accounts, the From picker and drafts' signing are
Advanced only; where accounts exist, Simple shows them only in the one balance with its "of which…" line and
as action-free Activity rows, a draft saying its signatures are collected in Advanced mode. -/
def testSimpleModeShowsAccountsOnlyInTheBalanceAndActivity : IO Unit := do
  let simple := modelWithAccounts false
  let home := rendered simple
  check "Simple home: the one balance" (contains home (satsText 70_000))
  check "Simple home: the of-which line" (contains home "of which" && contains home "accountsBalanceText")
  check "Simple home: the account's rows" (contains home "Household" && contains home "paymentAccount-aa")
  check "Simple home: a draft says where signatures are collected" (contains home "collected in Advanced mode")
  -- (the of-which line names "multisig account" and co-signers: that is the line the rule keeps)
  for needle in ["Ledger", "ledger", "Signers", "signersButton", "sendFrom", "\"From\"", "Sign and continue", "PSBT",
                 "Collect signatures", "Multisig", "multisigAccount-", "multisigBuildButton", "Register on"] do
    check s!"Simple home has no {needle}" (!contains home needle) (match home.splitOn needle with
      | a :: _ => (a.drop (a.length - 120)).toString | [] => "")
  -- account rows are there to read: no action on the draft or the account's row, the wallet's opens
  let draftRow := paymentRow simple simple.status.payments[0]!
  let accountRow := paymentRow simple simple.status.payments[1]!
  let walletRow := paymentRow simple simple.status.payments[2]!
  let actions (h : H) := (LeanNative.Html.toWire h).toJson.compress
  check "the draft row has no action" (!contains (actions draftRow) "\"button\"")
  check "the account row has no action" (!contains (actions accountRow) "\"button\"")
  check "the wallet's row opens its payment" (contains (actions walletRow) "\"button\"")
  -- the Send sheet itself (the home behind it was checked above)
  let sendModel := { simple with send := { inputs := { network := .signet, accountID := some "acct" } } }.present .send
  let send := (LeanNative.Html.toWire (sendSheet sendModel [])).toJson.compress
  for needle in ["Ledger", "Signers", "sendFrom", "\"From\"", "Sign and continue", "Household"] do
    check s!"Simple Send has no {needle}" (!contains send needle) (match send.splitOn needle with
      | a :: _ => (a.drop (a.length - 120)).toString | [] => "")
  check "a Simple review is always the wallet's" ((({ simple with send := { inputs := { accountID := some "acct" } } }).sendInputs.accountID).isNone)
  -- the same phone in Advanced mode shows them, so the checks above are not vacuous
  let advanced := modelWithAccounts true
  let wallet := rendered advanced
  check "Advanced Wallet tab: the Multisig section, the draft's step" (contains wallet "Multisig" && contains wallet "historyDraft-acct" &&
    contains wallet "1 of 2 signed")
  let sendTab := rendered (advanced.switchTab 1)
  check "Advanced Send tab: From" (contains sendTab "sendFromWallet" && contains sendTab "sendFrom-acct")
  let settings := rendered (advanced.switchTab 2)
  check "Advanced Settings: Signers" (contains settings "signersButton")

/-- The builder starts with this phone as its first member and any 2 of the members (upstream's builder
falls to any 1 when it seeds this phone). -/
def testTheBuilderStartsAtAnyTwoMembers : IO Unit := do
  let (m, _) := stepMultisig .openBuild (modelWithAccounts true)
  check "seeded with this phone" (m.multisigBuild.members.map (·.title) == ["This phone"])
  check "any 2 by default" (m.multisigBuild.threshold == 2 && m.multisigBuild.shownThreshold == 1)
  let f := (m.multisigBuild.addPick [{ key := "k2", label := "Bob" }] none none none).clamp .signet
  check "two members: any 2 of 2" (f.threshold == 2 && f.shownThreshold == 2)
  let f := (f.addPick [{ key := "k3", label := "Carol" }] none none none).clamp .signet
  check "three members: still any 2" (f.threshold == 2 && f.members.length == 3)

/-- Each Advanced-mode tab keeps its own navigation stack. -/
def testEachTabKeepsItsOwnStack : IO Unit := do
  let m := modelWithAccounts true
  let (m, _) := stepSigner .openSigners (m.switchTab 2)
  check "Settings pushed Signers" (m.routes == [.signers])
  let m := m.switchTab 0
  check "the Wallet tab has its own (empty) stack" m.routes.isEmpty
  let (m, _) := stepMultisig (.openAccount "acct") m
  let m := m.switchTab 2
  check "Settings got its stack back" (m.routes == [.signers])
  check "and Signers renders there" (contains (rendered m) "signersPairLedgerButton")
  let m := m.switchTab 0
  check "the Wallet tab its own" (m.routes == [.multisigAccount "acct"])

/-- One Send (PORT.md, deliberate departures, user 2026-10-28): the account page has no payment form; its
"Send from this account" opens the Send tab with the account under From, where an account with a recovery
path offers "Spend with" (Advanced only); a co-signer's PSBT is pasted from the page, and the descriptor is
shared with one button. -/
def testOneSendForAccounts : IO Unit := do
  let base := modelWithAccounts true
  let plain : MultisigInfo := { base.multisig.accounts[0]! with draft := none, recovery := some "after 144 blocks: any 1 of the signers" }
  let other : MultisigInfo := { plain with id := "solo", name := "Solo", recovery := none }
  -- in the foreground: the collection step takes answers only then
  let m := { base with multisig := { base.multisig with accounts := [plain, other] }, active := true }
  let (page, _) := stepMultisig (.openAccount "acct") m
  let shown := rendered page
  for needle in ["multisigSendButton", "Send from this account", "multisigPastePSBTButton", "Paste a PSBT from a co-signer",
                 "multisigShareButton", "Share with co-signers", "Everyone who signs needs this to see the account."] do
    check s!"the account page has {needle}" (contains shown needle)
  for needle in ["multisigAddressField", "multisigAmountField", "multisigFeeRateField", "multisigCreateButton", "Create PSBT",
                 "multisigPathPicker", "psbtPasteField", "\"multisigDescriptor\"", "multisigPSBTButton"] do
    check s!"the account page has no {needle}" (!contains shown needle)
  -- Send from this account: the Send tab, From the account; the account page stays on the Wallet tab's stack
  let (send, cs) := stepMultisig (.sendFrom "acct") page
  check "Send from this account: the Send tab" (send.tab == 1 && send.send.inputs.accountID == some "acct" && cs.length == 1)
  check "the Wallet tab keeps the account page" (send.savedRoutes 0 == [.multisigAccount "acct"])
  let tab := rendered send
  check "Send: Spend with, for an account with a recovery path" (contains tab "multisigPathPicker" && contains tab "Recovery path")
  check "Send: no recovery caption on the signers' path" (!contains tab "sendRecoveryNote")
  let (rec, _) := stepSend (.setRecovery true) send
  check "Spend with: the recovery path" rec.sendInputs.recovery
  check "the recovery caption" (contains (rendered rec) "Only coins that have not moved for the recovery delay can be spent this way")
  let (solo, _) := stepSend (.setSource (some "solo")) rec
  check "another account: the signers again, no picker" (!solo.sendInputs.recovery && !contains (rendered solo) "multisigPathPicker")
  let (wallet, _) := stepSend (.setSource none) rec
  check "the wallet: no picker" (!wallet.sendInputs.recovery && !contains (rendered wallet) "multisigPathPicker")
  let simple := { rec with settings := { rec.settings with advancedMode := false } }
  check "Simple: never the recovery path" (!simple.sendInputs.recovery && simple.sendInputs.accountID.isNone)
  -- a pasted co-signer's PSBT is filed at once, then the collection step opens
  let (pasting, cs) := onHost (.pasted (.accountPSBT "acct") "cHNidP8BAA") page
  check "the paste files the draft" (pasting.collect.busy && cs.any fun c => c matches .adoptDraft _ _ "acct" "cHNidP8BAA")
  let (opened, _) := onHost (.collected pasting.generation pasting.collect.epoch "acct" true) pasting
  check "then the collection step" (opened.routes == [.multisigAccount "acct", .multisigPSBT "acct"] && !opened.collect.busy)
  let (empty, _) := onHost (.pasted (.accountPSBT "acct") "  ") page
  check "an empty clipboard says so on the page" (contains (rendered empty) "The clipboard holds no PSBT.")
  -- with a draft, the page points at it instead
  let drafted := rendered (stepMultisig (.openAccount "acct") base).1
  check "a draft: Payment awaiting signatures" (contains drafted "multisigDraftButton" && !contains drafted "multisigSendButton")

/-- Plain wording for creating and joining (PORT.md, deliberate departures, user 2026-10-28). -/
def testPlainCreateAndJoinWording : IO Unit := do
  let m := modelWithAccounts true
  let wallet := rendered m
  for needle in ["Accounts that need more than one signature to spend.", "Create an account", "Join an account",
                 "You choose who signs, then share the account with them.", "Paste the account someone shared with you.",
                 "multisigBuildButton", "multisigAddButton"] do
    check s!"Wallet tab: {needle}" (contains wallet needle)
  check "Wallet tab: no jargon" (!contains wallet "k-of-n" && !contains wallet "Join with a descriptor")
  let (join, _) := stepMultisig .openAdd m
  let shown := rendered join
  for needle in ["Join an account", "Send this to whoever is creating the account.", "Paste the account (tr(…))",
                 "Winnow finds coins sent to it from now on.", "multisigKeyText", "multisigDescriptorField"] do
    check s!"Join: {needle}" (contains shown needle)
  for needle in ["Copy 2-of-2 template", "NUMS", "/<0;1>/* suffix", "Add multisig account"] do
    check s!"Join has no {needle}" (!contains shown needle)
  let (build, _) := stepMultisig .openBuild m
  check "Builder: Create an account" (contains (rendered build) "Create an account")

/-- The phone locks while the person approves on the Ledger, or while a payment broadcasts: the scene goes to
the background, which starts a new generation, and the answer comes back from the old one. It still lands
(0.9.1 left "Creating…" and "Sending…" up for good, with the payment sent); a network switch still drops it. -/
def testAnswersFinishAcrossTheBackground : IO Unit := do
  let m := modelWithAccounts true
  let building := { m with multisigBuild := { m.multisigBuild with name := "Pair", creating := true } }
  let g := building.generation
  let (away, _) := onHost (.scene false) building
  let (back, _) := onHost (.scene true) away
  check "the background started a new generation" (back.generation != g)
  let (done, cs) := onHost (.multisigCreated g "id1" "tr(…)" (some (.ok "nnn"))) back
  check "the account built before the background shows" (!done.multisigBuild.creating &&
    done.multisigBuild.created.any (·.1 == "id1") && done.multisigBuild.registration matches some (.ok "nnn"))
  check "the overview is asked for in the new generation" (cs.any fun | .multisigOverview g' => g' == back.generation | _ => false)
  check "and the screen says so" (contains (rendered (stepMultisig .openBuild done).1) "Create an account" &&
    !contains (rendered done) "Creating…")
  let (failed, _) := onHost (.failed g "multisigBuild" "the Ledger did not answer in time") back
  check "a failure from before the background shows too" (!failed.multisigBuild.creating &&
    failed.multisigBuild.error == some "the Ledger did not answer in time")
  -- pairing: the same
  let (pairing, _) := stepMultisig .openLedgerPair m
  let (pairing, _) := stepMultisig (.setLedgerName "nnn") pairing
  let (pairing, cs) := stepMultisig .pairLedger pairing
  let some pg := cs.findSome? fun | .pairLedger g' _ _ => some g' | _ => none
    | check "Pair a Ledger asks the backend" false
  let (paired, _) := onHost (.ledgerPaired pg "sig1") (onHost (.scene true) (onHost (.scene false) pairing).1).1
  check "pairing finished across the background" (!paired.ledgerPair.pairing && paired.routes.getLast? != some .ledgerPair)
  -- a payment broadcast while the phone was locked: the receipt shows and Send is free again
  let paying := { m with send := { m.send with sending := true }, spendingInFlight := true }
  let pg := paying.generation
  let (back, _) := onHost (.scene true) (onHost (.scene false) paying).1
  let (paid, cs) := onHost (.sent pg "tx1" []) back
  check "the payment's receipt shows after the background" (!paid.send.sending && paid.send.sentTxid == some "tx1")
  check "its follow-ups run in the new generation" (cs.any fun | .refresh g' => g' == back.generation | _ => false)
  -- another wallet: dropped
  let (other, _) := building.switchNetwork .mainnet
  let (other, _) := onHost (.multisigCreated g "id1" "tr(…)" none) { other with multisigBuild := building.multisigBuild }
  check "another network's wallet drops it" other.multisigBuild.created.isNone

def pureTests : List (String × IO Unit) :=
  [ ("testPaymentsMergeWalletAndAccountRowsAndFoldTransfers", testPaymentsMergeWalletAndAccountRowsAndFoldTransfers)
  , ("testAReviewForTheWalletNeverSignsForAnAccount", testAReviewForTheWalletNeverSignsForAnAccount)
  , ("testTheDraftRowShowsTheLeafClosestToFinishing", testTheDraftRowShowsTheLeafClosestToFinishing)
  , ("testSimpleModeShowsAccountsOnlyInTheBalanceAndActivity", testSimpleModeShowsAccountsOnlyInTheBalanceAndActivity)
  , ("testEachTabKeepsItsOwnStack", testEachTabKeepsItsOwnStack)
  , ("testOneSendForAccounts", testOneSendForAccounts)
  , ("testPlainCreateAndJoinWording", testPlainCreateAndJoinWording)
  , ("testTheBuilderStartsAtAnyTwoMembers", testTheBuilderStartsAtAnyTwoMembers)
  , ("testAnswersFinishAcrossTheBackground", testAnswersFinishAcrossTheBackground) ]

/-! ## Stores the Swift app left (`StoreSeal.setAsideSwiftEra`) -/

/-- The Keychain as the shell shows it: every item is bytes; `load` answers text items only, so the Swift
app's raw store key reads as absent, as `keychain.get` answers it no `value`; `loadBytes` sees every item.
A second item under a taken account fails as `SecItemAdd` does. -/
def shellLikeKeychain (ref : IO.Ref (Std.HashMap String ByteArray)) : Keys.KeyStore IO where
  store secret id := do
    if let some b := (← ref.get)[id]? then
      throw (if (String.fromUTF8? b).isSome then .alreadyExists id else .keychain (-25299))
    ref.modify (·.insert id secret.serialized)
  load id := do
    let some b := (← ref.get)[id]? | throw (.notFound id)
    let some t := String.fromUTF8? b | throw (.notFound id)
    match Keys.WalletSecret.parse t.toUTF8 with | .ok s => pure s | .error e => throw e
  delete id := ref.modify (·.erase id)
  loadBytes id := do return (← ref.get)[id]?
  storeBytes b id := do
    if (← ref.get).contains id then throw (.alreadyExists id)
    ref.modify (·.insert id b)

/-- A raw 32-byte key that is not UTF-8, as the Swift app's are in practice. -/
def swiftKey : IO ByteArray := do return (← IO.getRandomBytes 32).set! 0 0xFF

/-- What the Swift app left for `store`: its raw key in the Keychain and the file sealed under it. -/
def leaveSwiftStore (ref : IO.Ref (Std.HashMap String ByteArray)) (store : String) (payload : ByteArray)
    (path : System.FilePath) : IO (ByteArray × ByteArray) := do
  let key ← swiftKey
  ref.modify (·.insert s!"{accountPrefix}{store}.signet" key)
  let file := SealedStoreFile.sealed payload store signet key
  IO.FS.writeBinFile path file
  return (key, file)

/-- An upgraded phone: the Swift app's multisig accounts, signers and people are set aside, file and key,
and each store starts empty and takes changes, where before it read as damage and refused them (Pair a
Ledger: "Winnow could not safely read its signers"). -/
def testSwiftEraStoresAreSetAsideAndStartEmpty : IO Unit := do
  let ref ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let keys := StoreKeyVault.ofKeyStore (shellLikeKeychain ref)
  let a ← twoOfTwo
  let record := recordOf a #[← coin a 80_000]
  let url ← tempFile "multisig.json"
  let (key, file) ← leaveSwiftStore ref MultisigStore.storeName (MultisigStore.encode #[record]) url
  let (store, opened) ← S.open keys (some url)
  check "swift-era multisig: opens as a new store" (opened == .missing && !(← store.ref.get).isDamaged)
  check "swift-era multisig: no accounts" ((← store.all).isEmpty)
  let aside := url.withFileName "multisig.swift-era.json"
  check "swift-era multisig: the file is set aside unchanged"
    (!(← url.pathExists) && (← aside.pathExists) && (← IO.FS.readBinFile aside) == file)
  let held ← ref.get
  check "swift-era multisig: the key is kept beside, not deleted"
    (held["store-key.swift-era.multisig.signet"]? == some key && !held.contains "store-key.multisig.signet")
  need "swift-era multisig: an account can be added" (store.restore #[record])
  let (reopened, again) ← S.open keys (some url)
  check "swift-era multisig: the new store reopens loaded" (again == .loaded && (← reopened.all) == #[record])
  check "swift-era multisig: its key is this app's" ((← ref.get)["store-key.multisig.signet"]?.map (·.size) != some 32)
  check "swift-era multisig: the set-aside file is left alone" ((← IO.FS.readBinFile aside) == file)

  let signersURL ← tempFile "signers.json"
  discard <| leaveSwiftStore ref SignerStore.storeName (SignerStore.encode #[]) signersURL
  let (signers, signersOpened) ← SignerStore.configure keys (some signersURL) signet
  check "swift-era signers: opens as a new store" (signersOpened == .missing && !signers.isDamaged)
  check "swift-era signers: set aside" (← (signersURL.withFileName "signers.swift-era.json").pathExists)
  let bob ← keyExpression (← masters)[2]!
  let added ← (signers.addKeys keys writeAtomically "Bob" #[bob] "local-bob" 0).run
  check "swift-era signers: a signer can be saved" added.toBool

  let peopleURL ← tempFile "people.json"
  discard <| leaveSwiftStore ref PeopleStore.storeName (PeopleStore.encode #[] #[]) peopleURL
  let (people, peopleOpened) ← PeopleStore.configure keys (some peopleURL) signet
  check "swift-era people: opens as a new store" (peopleOpened == .missing && !people.isDamaged)
  check "swift-era people: set aside" (← (peopleURL.withFileName "people.swift-era.json").pathExists)

/-- A set-aside stopped after the key moved and before the file did finishes at the next open. -/
def testAnInterruptedSetAsideFinishes : IO Unit := do
  let ref ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let keys := StoreKeyVault.ofKeyStore (shellLikeKeychain ref)
  let url ← tempFile "multisig.json"
  let (key, file) ← leaveSwiftStore ref MultisigStore.storeName (MultisigStore.encode #[]) url
  ref.modify fun m => (m.erase "store-key.multisig.signet").insert "store-key.swift-era.multisig.signet" key
  let (store, opened) ← S.open keys (some url)
  check "interrupted: opens as a new store" (opened == .missing && !(← store.ref.get).isDamaged)
  let aside := url.withFileName "multisig.swift-era.json"
  check "interrupted: the file is set aside" (!(← url.pathExists) && (← IO.FS.readBinFile aside) == file)

/-- Only the Swift app's key is set aside: a store this app sealed whose file was changed still reads as
damage, and its file and key stay where they are. -/
def testATamperedFileUnderThisAppsKeyIsStillDamage : IO Unit := do
  let ref ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let keys := StoreKeyVault.ofKeyStore (shellLikeKeychain ref)
  let a ← twoOfTwo
  let url ← tempFile "multisig.json"
  let (store, _) ← S.open keys (some url)
  need "seal a store" (store.restore #[recordOf a #[← coin a 80_000]])
  let sealed ← IO.FS.readBinFile url
  let tampered := sealed.set! (sealed.size - 2) (sealed[sealed.size - 2]! ^^^ 0x01)
  IO.FS.writeBinFile url tampered
  let before ← ref.get
  let (_, opened) ← S.open keys (some url)
  check "tampered: reads as damage" (match opened with | .damaged _ => true | _ => false)
  check "tampered: the file stays" ((← IO.FS.readBinFile url) == tampered &&
    !(← (url.withFileName "multisig.swift-era.json").pathExists))
  check "tampered: the key stays" ((← ref.get)["store-key.multisig.signet"]? == before["store-key.multisig.signet"]? &&
    !(← ref.get).contains "store-key.swift-era.multisig.signet")

/-! ## main -/

def storeTests : List (String × IO Unit) :=
  [ ("testSwiftEraStoresAreSetAsideAndStartEmpty", testSwiftEraStoresAreSetAsideAndStartEmpty)
  , ("testAnInterruptedSetAsideFinishes", testAnInterruptedSetAsideFinishes)
  , ("testATamperedFileUnderThisAppsKeyIsStillDamage", testATamperedFileUnderThisAppsKeyIsStillDamage)
  , ("testBackupPreservesAccountsAndRejectsChangedOwnership", testBackupPreservesAccountsAndRejectsChangedOwnership)
  , ("testBackupCarriesPendingAccountPayments", testBackupCarriesPendingAccountPayments)
  , ("testPaymentsSpendsAndRollbacks", testPaymentsSpendsAndRollbacks)
  , ("testARollbackKeepsTheInputsOfAFallenSpendReserved", testARollbackKeepsTheInputsOfAFallenSpendReserved)
  , ("testARollbackKeepsAReservedCoinFromAFallenBlock", testARollbackKeepsAReservedCoinFromAFallenBlock)
  , ("testZeroValueOutputIsIgnoredAndTheScanMovesOn", testZeroValueOutputIsIgnoredAndTheScanMovesOn)
  , ("testALosingInFlightSpendReleasesItsCoinsAndDropsItsChange", testALosingInFlightSpendReleasesItsCoinsAndDropsItsChange)
  , ("testLookaheadFindsPaymentsUpToTheGapLimitAhead", testLookaheadFindsPaymentsUpToTheGapLimitAhead)
  , ("testTamperedUnsealedAndOversizedFilesAreRefusedAndKept", testTamperedUnsealedAndOversizedFilesAreRefusedAndKept)
  , ("testDuplicateWrongNetworkAndBadNamesAreRefused", testDuplicateWrongNetworkAndBadNamesAreRefused)
  , ("testDraftsFollowTheirCoinsAndAnAbandonedSpendFreesThem", testDraftsFollowTheirCoinsAndAnAbandonedSpendFreesThem)
  , ("testADraftConfirmedByACoSignerPaysItsPerson", testADraftConfirmedByACoSignerPaysItsPerson) ]

def main : IO UInt32 := do
  let root ← IO.FS.createTempDir
  tempRoot.set root
  IO.println s!"multisig-app-test in {root}"
  IO.println "MultisigStoreTests"
  for (name, t) in storeTests do runTest name t
  IO.println "MultisigAccountFlowTests"
  for (name, t) in flowTests do runTest name t
  IO.println "LedgerPairingTests, LedgerBluetoothTests"
  for (name, t) in ledgerTests do runTest name t
  IO.println "SignerRosterTests"
  for (name, t) in signerTests do runTest name t
  IO.println "NestedMultisigFlowTests"
  -- MULTISIG_APP_QUICK=1 (a pull request's CI) leaves out the two slowest flows, six minutes between them;
  -- multisig-differential's nested cases still run
  let quick := (← IO.getEnv "MULTISIG_APP_QUICK") == some "1"
  for (name, t) in nestedTests do
    if quick && name != "testPairingSavingAndRegisteringAreAdvancedModeOnly" then IO.println s!"  {name}: skipped (MULTISIG_APP_QUICK)"
    else runTest name t
  IO.println "MultisigAccountFlowTests (one wallet)"
  for (name, t) in oneWalletTests do runTest name t
  IO.println "HistoryDisplayTests, SendReviewBindingTests, draft rows"
  for (name, t) in pureTests do runTest name t
  try IO.FS.removeDirAll root catch _ => pure ()
  let failed ← failures.get
  IO.println s!"multisig-app-test: {← passed.get} passed, {failed.size} failed"
  -- Exit at once: the app's peer pools leave monitor tasks that sleep 30 s between checks, and the runtime
  -- waits for every task before the process ends.
  (← IO.getStdout).flush
  IO.Process.exit (if failed.isEmpty then 0 else 1)
