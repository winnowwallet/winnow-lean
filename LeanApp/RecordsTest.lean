import WinnowApp.Real.RecordsBackend
import WinnowApp.Real
import WinnowApp.View
import WinnowApp.E2E
import WinnowApp.Project
import ElmLean.Erase
import ElmLean.Json

/-! `records-test`: a scripted run of every records operation against a temporary directory, with the
in-memory key store and two wallets made by `Wallet.create` (two phones: A and B).

Covers people (add, rename, label, attach, remove), every kind of paste, receive and sender labels, store
tamper detection (on the sealed people file), a wrong-network store, a first write that fails, and
reopening everything from disk. Exits 1 on any failure. (The shared-savings and MuSig2 scenarios went with
vaults, upstream 1cf93fb; cards and records written with a `signerKey` still read.) -/

open Winnow WinnowApp WinnowApp.RecordsReal
open Tx (BitcoinNetwork)

structure T where
  passed : IO.Ref Nat
  failed : IO.Ref (Array String)

def T.check (t : T) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then t.passed.modify (· + 1)
  else
    t.failed.modify (·.push name)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

/-- Runs `x`; a failure is a test failure (and `none`). -/
def T.ok {α} (t : T) (name : String) (x : RM α) : IO (Option α) := do
  match ← x.run with
  | .ok a => t.check name true; return some a
  | .error e => t.check name false s!"{e.name}: {e.description}"; return none

/-- Runs `x`, expecting the failure `kind`. -/
def T.err {α} (t : T) (name kind : String) (x : RM α) : IO Unit := do
  match ← x.run with
  | .ok _ => t.check name false s!"expected {kind}, it succeeded"
  | .error e => t.check name (e.name == kind) s!"expected {kind}, got {e.name}: {e.description}"

def T.get {α} [Inhabited α] (t : T) (name : String) (x : RM α) : IO α := do
  match ← t.ok name x with
  | some a => return a
  | none => throw (IO.userError s!"cannot continue after {name}")

def network : BitcoinNetwork := .regtest

def wm {α} (x : WM α) : RM α := liftWallet network x

def coinbaseInput : Transaction.Input :=
  { previousOutput := ⟨ByteArray.mk (Array.replicate 32 0), 0xFFFF_FFFF⟩, scriptSig := ByteArray.mk #[0x01], sequence := 0xFFFF_FFFF }

def fakeMatch (height : UInt32) (txs : Array Transaction) : Net.BlockMatch :=
  let header : Net.BlockHeader := {
    version := 2, previousHash := ByteArray.mk (Array.replicate 32 0),
    merkleRoot := ByteArray.mk (Array.replicate 32 0xAA), time := 1_700_000_000 + height, bits := 0x207F_FFFF, nonce := 0,
    hash := .empty }
  { height := height, blockHash := .empty, block := { header := header, transactions := txs } }

/-- A block at `height` whose second transaction pays `outputs` (the first is an unrelated coinbase). -/
def fundingBlock (height : UInt32) (seed : UInt8) (outputs : Array (ByteArray × Int64)) : Net.BlockMatch :=
  let coinbase : Transaction := {
    version := 2, inputs := #[coinbaseInput],
    outputs := #[{ value := 50, scriptPubKey := ByteArray.mk #[0x6a] }], locktime := height }
  let funding : Transaction := {
    version := 2,
    inputs := #[{ previousOutput := ⟨ByteArray.mk (Array.replicate 32 seed), 0⟩, scriptSig := .empty, sequence := 0xFFFF_FFFD }],
    outputs := outputs.map fun (s, v) => { value := v, scriptPubKey := s }, locktime := 0 }
  fakeMatch height #[coinbase, funding]

structure Phone where
  name : String
  dir : System.FilePath
  secrets : IO.Ref Keys.InMemorySecrets
  wallet : Wallet
  store : RecordsStore

def Phone.keyStore (p : Phone) : Keys.KeyStore IO := inMemoryKeyStore p.secrets
def Phone.keys (p : Phone) : StoreKeyVault := StoreKeyVault.ofKeyStore p.keyStore

def newPhone (root : System.FilePath) (name : String) : IO Phone := do
  let dir := root / name / "regtest"
  IO.FS.createDirAll dir
  let secrets ← IO.mkRef ({} : Keys.InMemorySecrets)
  let ks := inMemoryKeyStore secrets
  let wallet ← match ← (Wallet.create network ks (some (dir / "wallet.json"))).run with
    | .ok w => pure w
    | .error e => throw (IO.userError s!"Wallet.create: {e.name}")
  let store ← RecordsStore.open network (some dir) (StoreKeyVault.ofKeyStore ks)
  return { name, dir, secrets, wallet, store }

def Phone.reopen (p : Phone) : IO Phone := do
  return { p with store := ← RecordsStore.open network (some p.dir) p.keys }

def Phone.records (p : Phone) : IO Records := RecordsReal.records p.store (some p.wallet)

def mutateByte (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b[i]! ^^^ 0x01)

/-! ## The script -/

def peopleAndPastes (t : T) (a b : Phone) : IO Unit := do
  -- cards and own keys
  let cardB ← t.get "ownCard B" (do return (← ownPersonCard b.wallet "Bob").serialized)
  let keyB ← t.get "ownKeyExpression B" (ownKeyExpression b.wallet false)
  let keyBm ← t.get "ownKeyExpression B multipath" (ownKeyExpression b.wallet true)
  t.check "own key expression shape" (keyB.startsWith "[" && (keyB.splitOn "/86'/1'/0']tpub").length == 2 && keyBm == keyB ++ "/<0;1>/*") keyB
  -- pastes of each kind
  let pCard ← t.get "paste card" (parsePaste network cardB)
  t.check "paste card reads name and fresh pay-to" (pCard.name == some "Bob" && pCard.payTo == some true)
  let pKey ← t.get "paste key expression" (parsePaste network keyB)
  t.check "paste bare key: fresh pay-to" (pKey.payTo == some true && pKey.name.isNone)
  let pKeyM ← t.get "paste multipath key" (parsePaste network keyBm)
  t.check "paste multipath key" (pKeyM.payTo == some true)
  let pDesc ← t.get "paste descriptor" (parsePaste network s!"tr({keyBm})")
  t.check "paste descriptor: pay-to" (pDesc.payTo == some true)
  let addrB ← t.get "B address" (wm (b.wallet.address .receive 7))
  let pAddr ← t.get "paste address" (parsePaste network addrB)
  t.check "paste address: one address" (pAddr.payTo == some false)
  t.err "paste empty" "empty" (parsePaste network "   ")
  t.err "paste garbage" "unrecognised" (parsePaste network "hello world")
  t.err "paste mainnet address on regtest" "wrongNetwork" (parsePaste network "bc1qar0srrr7xfkvy5l643lydnw9re59gtzzwf5mdq")
  let otherNet ← t.get "card for another network" (do
    let c := PersonCard.make .mainnet "Eve" none
    return c.serialized)
  t.err "paste card of another network" "wrongNetwork" (parsePaste network otherNet)
  -- a card from a Winnow that also shared a signer key still reads; the key is ignored
  let oldCard := s!"\{\"name\":\"Bob\",\"network\":\"regtest\",\"payTo\":\"tr({keyBm})\",\"signerKey\":\"{keyBm}\",\"version\":1,\"winnow\":\"person-card\"}"
  let pOld ← t.get "paste a card that carries a signer key" (parsePaste network oldCard)
  t.check "the old card reads as a pay-to card" (pOld.name == some "Bob" && pOld.payTo == some true)
  t.check "a stored person's signerKey is ignored, and never written back"
    (match SwiftJSON.decodeText s!"\{\"id\":\"p\",\"name\":\"Old\",\"nextPaymentIndex\":0,\"signerKey\":\"{keyBm}\"}" PersonRecord.ofJV with
     | .ok r => r.payTo.isNone && SwiftJSON.write r.toJV == "{\"id\":\"p\",\"name\":\"Old\",\"nextPaymentIndex\":0}"
     | .error _ => false)
  -- add / rename / duplicates
  let r ← t.get "add Bob from card" (addPerson a.store (some a.wallet) "Bob" (some cardB) none none none)
  let some bob := r.people.find? (·.name == "Bob") | t.check "Bob saved" false; return
  t.check "Bob is paid at fresh addresses" (bob.payTo == some true)
  t.check "recipientByScript covers Bob's first scripts" ((r.recipientByScript.filter (·.2 == bob.id)).length == 20)
  t.err "duplicate card refused" "duplicate" (addPerson a.store (some a.wallet) "Bobby" (some cardB) none none none)
  t.err "a name over two lines is refused" "invalidState" (addPerson a.store (some a.wallet) "Bo\nb" (some addrB) none none none)
  let r ← t.get "rename Bob" (updateRecipient a.store (some a.wallet) bob.id (some "Robert") true)
  t.check "renamed" ((r.people.find? (·.id == bob.id)).map (·.name) == some "Robert")
  let r ← t.get "add Carol from an address" (addPerson a.store (some a.wallet) "Carol" (some addrB) none none none)
  let some carol := r.people.find? (·.name == "Carol") | t.check "Carol saved" false; return
  t.check "Carol pays one address" (carol.payTo == some false)
  -- sender labels
  let txid := hex (ByteArray.mk (Array.replicate 32 0x5a))
  let r ← t.get "add Dave as the sender of a payment" (addPerson a.store (some a.wallet) "Dave" none none none (some txid))
  let some dave := r.people.find? (·.name == "Dave") | t.check "Dave saved" false; return
  t.check "Dave is name-only and labels the payment" (dave.payTo.isNone && r.senderByTxid == [(txid, dave.id)])
  t.err "label with an unknown person" "unknownPerson" (labelSender a.store (some a.wallet) txid "nobody")
  t.err "label with an invalid txid" "invalidState" (labelSender a.store (some a.wallet) "abcd" dave.id)
  t.err "a sender with an invalid txid" "invalidState" (addPerson a.store (some a.wallet) "Eve" none none none (some "abcd"))
  let r ← RM.toIO (RM.io (RecordsReal.records a.store (some a.wallet)))
  t.check "the person is saved even when the label is refused (as AppModel's two steps)" (r.people.any (·.name == "Eve"))
  let some eve := r.people.find? (·.name == "Eve") | t.check "Eve saved" false; return
  let aR ← a.reopen
  t.check "and disk agrees with memory" ((← RecordsReal.records aR.store (some a.wallet)).people.any (·.name == "Eve"))
  discard <| t.get "remove Eve" (removePerson a.store (some a.wallet) eve.id)
  let addrB2 ← t.get "B address 8" (wm (b.wallet.address .receive 8))
  let r ← t.get "attach a funding address to Dave" (attachDestination a.store (some a.wallet) dave.id addrB2 .localFunding (some txid))
  t.check "Dave now has an unverified funding destination"
    (((r.people.find? (·.id == dave.id)).map fun p => p.payTo == some false && p.provenance == some .localFunding) == some true)
  t.err "a second destination is refused" "invalidState" (attachDestination a.store (some a.wallet) dave.id addrB .supplied none)
  let r ← t.get "remove the sender label" (removeSenderLabel a.store (some a.wallet) txid)
  t.check "label removed" r.senderByTxid.isEmpty
  discard <| t.get "label again" (labelSender a.store (some a.wallet) txid dave.id)
  let r ← t.get "remove Dave" (removePerson a.store (some a.wallet) dave.id)
  t.check "removing a person prunes their labels" (r.senderByTxid.isEmpty && !(r.people.any (·.id == dave.id)))
  let r ← t.get "remove Carol" (removePerson a.store (some a.wallet) carol.id)
  t.check "Carol removed" (!(r.people.any (·.id == carol.id)))
  t.err "remove twice" "unknownPerson" (removePerson a.store (some a.wallet) carol.id)
  -- hide and re-save a recipient keeps the record
  let r ← t.get "hide Robert" (updateRecipient a.store (some a.wallet) bob.id none false)
  t.check "hidden" (((r.people.find? (·.id == bob.id)).map (·.isSavedRecipient)) == some false)
  let r ← t.get "re-saving the hidden card restores it" (addPerson a.store (some a.wallet) "Bob" (some cardB) none none none)
  t.check "same record, saved again, renamed" (((r.people.find? (·.id == bob.id)).map fun p => p.isSavedRecipient && p.name == "Bob") == some true)
  -- B knows A too
  let cardA ← t.get "ownCard A" (do return (← ownPersonCard a.wallet "Alice").serialized)
  discard <| t.get "B adds Alice" (addPerson b.store (some b.wallet) "Alice" (some cardA) none none none)

def receiveLabels (t : T) (a b : Phone) : IO Unit := do
  let addr ← t.get "A receive address" (wm (a.wallet.address .receive 0))
  let foreign ← t.get "B receive address" (wm (b.wallet.address .receive 0))
  let r ← t.get "set a receive label" (setReceiveLabel a.store a.wallet addr "Invoice 12")
  t.check "label shown by address" (r.receiveLabels == [(addr, "Invoice 12")])
  t.err "a label for someone else's address is refused" "noWallet"
    (setReceiveLabel a.store a.wallet foreign "x")
  t.err "a two-line label is refused" "invalidLabel" (setReceiveLabel a.store a.wallet addr "a\nb")
  let addr1 ← t.get "A receive address 1" (wm (a.wallet.address .receive 1))
  discard <| t.get "second label" (setReceiveLabel a.store a.wallet addr1 "  Rent  ")
  let r ← t.get "empty text removes a label" (setReceiveLabel a.store a.wallet addr "")
  t.check "one label left, trimmed" (r.receiveLabels == [(addr1, "Rent")])
  let file ← IO.FS.readFile (a.dir / "receive-labels.json")
  let script ← t.get "script of address 1" (RM.lift (fun e => namedError e.name network) (AddressDecoder.scriptPubKey addr1 network))
  t.check "labels file in the Swift shape"
    (file == s!"\{\"labels\":\{\"{hex script}\":\"Rent\"},\"network\":\"regtest\",\"version\":1,\"walletID\":\"{a.wallet.id}\"}") file

def lookupSenderTest (t : T) (b : Phone) : IO Unit := do
  let txid := hex (ByteArray.mk (Array.replicate 32 0x11))
  let funder ← t.get "B address 9" (wm (b.wallet.address .receive 9))
  let answer := s!"\{\"txid\":\"{txid}\",\"vin\":[\{\"prevout\":\{\"scriptpubkey_address\":\"{funder}\"}},\{\"prevout\":null},\{\"prevout\":\{\"scriptpubkey_address\":\"{funder}\"}}]}"
  let urls ← IO.mkRef ([] : List String)
  let get : String → Nat → IO ByteArray := fun url _ => do urls.modify (url :: ·); return answer.toUTF8
  let addrs ← t.get "lookupSender" (lookupSender get network txid "https://example.org/api/")
  t.check "distinct funding addresses, in input order" (addrs == [funder])
  t.check "GET {base}/tx/{txid}" ((← urls.get) == [s!"https://example.org/api/tx/{txid}"])
  let other : String → Nat → IO ByteArray := fun _ _ => return "{\"txid\":\"00\",\"vin\":[]}".toUTF8
  t.err "a different transaction is refused" "unavailable" (lookupSender other network txid "https://example.org/api")
  let bad : String → Nat → IO ByteArray := fun _ _ => return "[]".toUTF8
  t.err "a wrong shape is refused" "unavailable" (lookupSender bad network txid "https://example.org/api")
  t.err "an invalid txid is refused" "unavailable" (lookupSender get network "abc" "https://example.org/api")

def tamper (t : T) (root : System.FilePath) (a : Phone) : IO Unit := do
  -- tampered people.json: a notice, and every mutation refused
  let peoplePath := a.dir / "people.json"
  let good ← IO.FS.readBinFile peoplePath
  t.check "people.json is sealed" (SealedStoreFile.isSealed good)
  IO.FS.writeBinFile peoplePath (mutateByte good (good.size - 3))
  let a2 ← a.reopen
  let r ← a2.records
  t.check "tampered people: unverified notice, no people"
    (r.peopleStorageNotice == some PeopleStore.unverifiedStorageMessage && r.people.isEmpty)
  t.err "a damaged people store refuses mutations" "damaged"
    (addPerson a2.store (some a.wallet) "Zed" none none none (some (hex (ByteArray.mk (Array.replicate 32 1)))))
  IO.FS.writeBinFile peoplePath good
  -- unsealed file while a key exists
  match SealedStoreFile.open good "people" network ((← (a.keys.key "people.regtest").run).toOption.join.getD .empty) with
  | .ok payload =>
    IO.FS.writeBinFile peoplePath payload
    let a3 ← a.reopen
    t.check "an unsealed file once a key exists reads as unverified"
      ((← a3.records).peopleStorageNotice == some PeopleStore.unverifiedStorageMessage)
    -- a valid seal around invalid content is damage, not substitution
    let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
    IO.FS.writeBinFile peoplePath (SealedStoreFile.sealed "{\"people\":[{\"id\":\"x\"}]}".toUTF8 "people" network key)
    let a4 ← a.reopen
    t.check "valid seal, invalid records: the damaged message"
      ((← a4.records).peopleStorageNotice == some PeopleStore.damagedStorageMessage)
  | .error e => t.check "own people file opens" false e.name
  IO.FS.writeBinFile peoplePath good
  let unverified (st : RecordsStore) : IO Bool := do
    return (← RecordsReal.records st none).peopleStorageNotice == some PeopleStore.unverifiedStorageMessage
  let peopleKey := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  -- a file sealed for another store name (the seal binds the store)
  match SealedStoreFile.open good "people" network peopleKey with
  | .ok payload =>
    IO.FS.writeBinFile peoplePath (SealedStoreFile.sealed payload "vaults" network peopleKey)
    t.check "a file sealed for another store is refused" (← unverified (← a.reopen).store)
  | .error e => t.check "own people file opens" false e.name
  IO.FS.writeBinFile peoplePath good
  -- wrong network, same device: a regtest file under signet, where signet has a key
  let sigDir := root / "A-signet"
  IO.FS.createDirAll sigDir
  let sig ← RecordsStore.open .signet (some sigDir) a.keys
  discard <| t.get "signet store's first write establishes its key"
    (addPerson sig none "Sam" none none none (some (hex (ByteArray.mk (Array.replicate 32 2)))))
  IO.FS.writeBinFile (sigDir / "people.json") good
  t.check "a regtest people file under signet fails verification" (← unverified (← RecordsStore.open .signet (some sigDir) a.keys))
  -- wrong network, fresh device: sealed file, no key at all
  let fresh ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let freshDir := root / "fresh"
  IO.FS.createDirAll freshDir
  IO.FS.writeBinFile (freshDir / "people.json") good
  t.check "a sealed file without its key is refused (keyMissing)"
    (← unverified (← RecordsStore.open network (some freshDir) (StoreKeyVault.inMemory fresh)))
  -- a file from before sealing is adopted and sealed
  let legacyDir := root / "legacy"
  IO.FS.createDirAll legacyDir
  let legacyKeys ← IO.mkRef ({} : Std.HashMap String ByteArray)
  match SealedStoreFile.open good "people" network peopleKey with
  | .ok payload =>
    IO.FS.writeBinFile (legacyDir / "people.json") payload
    let ls ← RecordsStore.open network (some legacyDir) (StoreKeyVault.inMemory legacyKeys)
    let r ← RecordsReal.records ls none
    t.check "an unsealed legacy file loads" r.peopleStorageNotice.isNone
    t.check "and is sealed now" (SealedStoreFile.isSealed (← IO.FS.readBinFile (legacyDir / "people.json")))
    t.check "with its people" (!r.people.isEmpty)
  | .error e => t.check "own people file opens" false e.name
  -- a first write that fails discards the new key
  let failKeys ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let failDir := root / "fail"
  IO.FS.createDirAll failDir
  let fs ← RecordsStore.open network (some failDir) (StoreKeyVault.inMemory failKeys)
    (writeData := fun _ _ => throw (IO.userError "disk full"))
  t.err "a failed first write fails" "ioError"
    (addPerson fs none "Nia" none none none (some (hex (ByteArray.mk (Array.replicate 32 3)))))
  t.check "and leaves no key behind" (!(← failKeys.get).contains "people.regtest")
  t.check "and no person" (← records fs none).people.isEmpty
  -- a damaged label file: a notice, sets refused
  let labelsPath := a.dir / "receive-labels.json"
  let lgood ← IO.FS.readBinFile labelsPath
  IO.FS.writeBinFile labelsPath "{\"version\":2}".toUTF8
  let a5 ← a.reopen
  let r ← a5.records
  t.check "damaged labels: notice" (r.receiveLabelStorageNotice == some (RecordsError.labels .damaged).description && r.receiveLabels.isEmpty)
  let addr ← t.get "address" (wm (a.wallet.address .receive 2))
  t.err "a damaged label store refuses sets" "damaged" (setReceiveLabel a5.store a.wallet addr "x")
  IO.FS.writeBinFile labelsPath lgood

def reopenFromDisk (t : T) (a : Phone) (before : Records) : IO Unit := do
  let a2 ← a.reopen
  let r ← a2.records
  t.check "reopen: the same people" (r.people == before.people) s!"{reprStr r.people}"
  t.check "reopen: the same labels" (r.receiveLabels == before.receiveLabels && r.senderByTxid == before.senderByTxid)
  t.check "reopen: no notices" (r.peopleStorageNotice.isNone && r.receiveLabelStorageNotice.isNone)
  -- the people file is exactly what the Swift encoder writes for these records
  let st ← a2.store.read
  let file ← IO.FS.readBinFile (a.dir / "people.json")
  let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  t.check "people.json: seal over the sorted-key envelope"
    (file == SealedStoreFile.sealed (PeopleStore.encode st.people.records st.people.senderByTxid) "people" network key)

/-- Upstream d2ca878's `BackgroundSyncTests`: Simple mode waits out dropped peers but shows other errors at
once, and only link failures count as transient. -/
def syncErrorBookkeeping (t : T) : IO Unit := do
  let dropped := (Winnow.IO.NetError.peer (.disconnected "closed")).description
  t.check "simple sync error: none without an error" (simpleSyncError none none 0 == none)
  t.check "simple sync error: one dropped peer stays quiet" (simpleSyncError (some dropped) (some dropped) 1 == none)
  t.check "simple sync error: two dropped peers stay quiet" (simpleSyncError (some dropped) (some dropped) 2 == none)
  t.check "simple sync error: a third is said in plain words" (simpleSyncError (some dropped) (some dropped) 3 ==
    some "Winnow keeps losing its connection to Bitcoin peers. It will keep trying.")
  let mismatch := (Winnow.IO.NetError.filters (.filterHeaderMismatch 7)).description
  t.check "simple sync error: another failure shows as is" (simpleSyncError (some mismatch) (some dropped) 1 == some mismatch)
  t.check "simple sync error: a lone failure shows as is" (simpleSyncError (some mismatch) none 0 == some mismatch)
  t.check "transient: a dropped peer" (isTransientSyncError (.peer (.disconnected "closed")))
  t.check "transient: a timeout" (isTransientSyncError (.peer .timeout))
  t.check "transient: peers cooling down" (isTransientSyncError (.filters (.peersCoolingDown 2)))
  t.check "transient: no peers" (isTransientSyncError (.filters .noPeers))
  t.check "not transient: a protocol violation" (!isTransientSyncError (.peer (.protocolViolation "bad")))
  t.check "not transient: a checkpoint mismatch" (!isTransientSyncError (.filters (.checkpointMismatch "split")))
  t.check "not transient: a corrupt file" (!isTransientSyncError (.other "The file couldn’t be opened because it isn’t in the correct format."))

/-! ## Peer gateways (upstream d2ca878 `PeerGatewayModelTests`) -/

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

open Winnow.IO in
def discoveredTor : PeerGatewayConfiguration := { networks := [.tor], torProxy := some { host := "100.75.175.127", port := 9050 } }

/-- A backend core over nothing (no peer, no HTTPS): routing is all these tests drive. -/
def gatewayEnv (discover : Option (IO Winnow.IO.PeerGatewayConfiguration)) : IO Real.Env := do
  let ks := Winnow.inMemoryKeyStore (← IO.mkRef {})
  let env ← Real.Env.new { keyStore := ks, fetch := fun _ => throw (.other "offline"), discoverGateways := discover }
  return env

def relaunch (s : Settings) : Settings :=
  match Lean.Json.parse (Lean.toJson s).compress >>= Lean.fromJson? with
  | .ok s' => s'
  | .error _ => {}

open Winnow.IO in
def peerGatewayModel (t : T) : IO Unit := do
  -- testAutomaticDefaultAndManualOverridePersistAcrossModes
  let m : Model := { stage := .ready, settings := { advancedMode := true } }
  t.check "gateways: Automatic by default" (m.settings.peerGatewaySettings.mode == "automatic" && (relaunch {}).peerGatewaySettings == {})
  let m := m.loadGatewayDraft
  let config : PeerGatewayConfiguration := { networks := [.i2p], i2pProxy := some { host := "gateway", port := 4447 } }
  let m := (stepSettings (.setGatewayMode 2) m).1
  let m := (stepSettings (.setGatewayNetwork .clearnet false) m).1
  let m := (stepSettings (.setGatewayNetwork .i2p true) m).1
  let m := (stepSettings (.setI2PAddress "gateway:4447") m).1
  let (m, cs) := stepSettings .applyGateways m
  t.check "gateways: Apply saves the manual gateways" (m.settings.peerGatewaySettings == { mode := "manual", manual := config })
    (reprStr m.settings.peerGatewaySettings)
  t.check "gateways: Apply saves and reconnects" (cs.length == 2 && cs.any (· matches .reconnect ..) && cs.any (· matches .saveSettings _))
  let m := (step (.setAdvanced false) m).1
  let relaunched := relaunch m.settings
  t.check "gateways: the manual override survives Simple mode and a relaunch" (relaunched.peerGatewaySettings == { mode := "manual", manual := config })
  let http ← RoutedHTTPClient.ofGateways (fun _ => throw (.other "offline")) relaunched.peerGatewaySettings.initialActive
  t.check "gateways: I2P alone makes no HTTP request" (!http.enabled)
  let m := { m with settings := { m.settings with advancedMode := true } }.loadGatewayDraft
  let m := (stepSettings (.setGatewayNetwork .i2p false) m).1
  let (bad, badCmds) := stepSettings .applyGateways m
  t.check "gateways: an invalid edit does not overwrite the settings"
    (bad.settings.peerGatewaySettings.manual == config && badCmds.isEmpty &&
     bad.settingsDraft.gatewayError == some PeerGatewayConfiguration.Invalid.configuration.description)
  let (typo, _) := stepSettings .applyGateways (stepSettings (.setI2PAddress "gateway") (stepSettings (.setGatewayNetwork .i2p true) m).1).1
  t.check "gateways: an incomplete address is refused" (typo.settingsDraft.gatewayError == some PeerGatewayConfiguration.Invalid.address.description &&
    typo.settings.peerGatewaySettings.manual == config)
  let (direct, _) := stepSettings .applyGateways (stepSettings (.setGatewayMode 1) m).1
  t.check "gateways: Direct only persists" ((relaunch direct.settings).peerGatewaySettings.mode == "direct")
  t.check "gateways: Direct only keeps the manual gateways for later" ((relaunch direct.settings).peerGatewaySettings.manual == config)
  -- testRoutingBannerSaysWhetherPeersSeeTheIPAddress
  let tor : Winnow.Net.PeerEndpoint := { host := "100.75.175.127", port := 9050 }
  let i2p : Winnow.Net.PeerEndpoint := { host := "100.74.30.8", port := 4447 }
  let state (mode : String) (c : PeerGatewayConfiguration) (discovering := false) := PeerRoutingState.current mode c discovering
  t.check "banner: Tor and I2P" (state "automatic" { networks := [.tor, .i2p], torProxy := some tor, i2pProxy := some i2p } == .overlay true true)
  t.check "banner: Tor" (state "automatic" { networks := [.tor], torProxy := some tor } == .overlay true false)
  t.check "banner: Automatic found nothing" (state "automatic" {} == .direct true)
  t.check "banner: Direct only" (state "direct" {} == .direct false)
  t.check "banner: mixed" (state "manual" { networks := [.clearnet, .i2p], i2pProxy := some i2p } == .mixed)
  t.check "banner: checking" (state "automatic" {} true == .checking)
  t.check "banner: offline" (state "manual" { networks := [] } == .offline)
  t.check "banner: the private line" ((PeerRoutingState.overlay true true).message == "Private: peers reached through Tor and I2P")
  t.check "banner: a fallback says the IP is seen" (contains (PeerRoutingState.direct true).message "can see your IP address")
  t.check "banner: mixed says the IP is seen" (contains PeerRoutingState.mixed.message "can see your IP address")
  let banner := (ElmLean.Html.toWire (.list (beginnerSections { m with settings := { network := .mainnet } }) : H)).toJson.compress
  t.check "banner: Simple mode shows it on mainnet" (contains banner "peerRoutingBanner" && contains banner "Direct: peers can see your IP address. No Tor")
  let signet := (ElmLean.Html.toWire (.list (beginnerSections { m with settings := { network := .signet } }) : H)).toJson.compress
  t.check "banner: not on signet" (!contains signet "peerRoutingBanner")
  -- testCandidateCountFollowsRoutedNetworks
  let entry : CensusEntry := { host := "8.8.8.8", port := 8333, userAgent := "/Satoshi:30/", startHeight := 900_000 }
  let nets := #[("clearnet", #[entry, entry]), ("tor", #[entry]), ("i2p", #[entry, entry, entry])]
  let catalog : CensusCatalog := { date := "2026-09-28", tip := 900_000, networks := nets }
  t.check "candidates: clearnet" (Real.candidateCount catalog == "2 candidates")
  t.check "candidates: I2P" (Real.candidateCount catalog [.i2p] == "3 candidates")
  t.check "candidates: Tor" (Real.candidateCount catalog [.tor] == "1 candidate")
  t.check "candidates: all three" (Real.candidateCount catalog [.clearnet, .tor, .i2p] == "6 candidates")
  -- testCorruptSavedSettingsStayOffline
  let corrupt : Settings := match Lean.Json.parse "{\"peerGatewaySettings\":\"broken\"}" >>= Lean.fromJson? with
    | .ok s => s | .error _ => {}
  t.check "corrupt settings: read as offline" (corrupt.peerGatewaySettings == PeerGatewaySettings.unreadable)
  let env ← gatewayEnv (some (pure discoveredTor))
  env.modify (·.withSettings corrupt)
  Real.preparePeerGateways env
  let c ← env.get
  t.check "corrupt settings: networking stays offline" (!c.activeGateways.isValid && !c.http.enabled)
  -- testDiscoveredAddressesAreNotPersisted
  let env ← gatewayEnv (some (pure discoveredTor))
  let saved : Settings := {}
  env.modify (·.withSettings saved)
  Real.preparePeerGateways env
  let c ← env.get
  t.check "discovery: the gateways found are in use" (c.activeGateways == discoveredTor && c.http.proxy == discoveredTor.torProxy)
  t.check "discovery: nothing is persisted" (!contains (Lean.toJson saved).compress "100.75.175.127")
  let fresh ← gatewayEnv none
  t.check "discovery: a relaunch starts from clearnet" ((← fresh.get).activeGateways == {})
  -- testDiscoveryIsSharedUntilTheNetworkingGenerationEnds
  let asked ← IO.mkRef 0
  let gate ← IO.mkRef (← IO.Promise.new : IO.Promise PeerGatewayConfiguration)
  let discover : IO PeerGatewayConfiguration := do
    asked.modify (· + 1)
    let p ← gate.get
    return (← IO.wait p.result?).getD {}
  let env ← gatewayEnv (some discover)
  env.modify (·.withSettings {})
  let first ← IO.asTask (Real.preparePeerGateways env)
  while (← asked.get) == 0 do IO.sleep 5
  let second ← IO.asTask (Real.preparePeerGateways env)
  IO.sleep 50
  t.check "discovery: Checking while it runs" (← env.get).discoveringGateways
  (← gate.get).resolve discoveredTor
  discard <| IO.wait first
  discard <| IO.wait second
  Real.preparePeerGateways env
  t.check "discovery: one discovery for every caller of a generation" ((← asked.get) == 1 && (← env.get).activeGateways == discoveredTor)
  t.check "discovery: done" (!(← env.get).discoveringGateways)
  gate.set (← IO.Promise.new)
  Real.stopNetworking env
  let next ← IO.asTask (Real.preparePeerGateways env)
  while (← asked.get) < 2 do IO.sleep 5
  (← gate.get).resolve {}
  discard <| IO.wait next
  t.check "discovery: the next generation asks again" ((← asked.get) == 2 && (← env.get).activeGateways == {})
  -- testBackgroundAndManualChangeDiscardStaleDiscovery
  for changeMode in [false, true] do
    let gate ← IO.Promise.new
    let started ← IO.mkRef false
    let env ← gatewayEnv (some do started.set true; return (← IO.wait gate.result?).getD {})
    env.modify (·.withSettings {})
    let task ← IO.asTask (Real.preparePeerGateways env)
    while !(← started.get) do IO.sleep 5
    if changeMode then Real.reconnect env { peerGatewaySettings := { mode := "direct" } }
    else Real.stopNetworking env
    gate.resolve discoveredTor
    discard <| IO.wait task
    let c ← env.get
    t.check s!"stale discovery is dropped ({if changeMode then "mode change" else "background"})"
      (c.activeGateways == {} && !c.discoveringGateways)
  -- AppModel.backgroundRoutingAllowed (BackgroundSyncTests)
  let torGw : Winnow.Net.PeerEndpoint := { host := "100.64.0.1", port := 9050 }
  let i2pGw : Winnow.Net.PeerEndpoint := { host := "100.64.0.2", port := 4447 }
  let overlay : PeerGatewayConfiguration := { networks := [.tor, .i2p], torProxy := some torGw, i2pProxy := some i2pGw }
  t.check "background: no direct connection after the foreground used gateways" (!backgroundRoutingAllowed "automatic" {} true)
  t.check "background: through the gateways found" (backgroundRoutingAllowed "automatic" overlay true)
  t.check "background: direct when the foreground was direct too" (backgroundRoutingAllowed "automatic" {} false)
  t.check "background: Direct only as chosen" (backgroundRoutingAllowed "direct" {} true)
  t.check "background: Manual as chosen" (backgroundRoutingAllowed "manual" overlay true)

/-- Sync bookkeeping as the screens show it (upstream 66c6a48): Simple mode waits out dropped peers, Advanced
shows every error; Advanced's Sync section says when the chain was last checked. -/
def syncBookkeepingScreens (t : T) : IO Unit := do
  let dropped := (Winnow.IO.NetError.peer (.disconnected "closed")).description
  let status (n : Nat) : Status := { lastSyncError := some dropped, transientSyncError := some dropped, transientSyncFailures := n }
  let simple (n : Nat) := (ElmLean.Html.toWire (.list (beginnerSections { stage := .ready, status := status n }) : H)).toJson.compress
  let advanced (n : Nat) := (ElmLean.Html.toWire (.list (walletSections { stage := .ready, settings := { advancedMode := true }, status := status n }) : H)).toJson.compress
  t.check "Simple mode: a dropped peer stays quiet" (!contains (simple 1) "closed")
  t.check "Simple mode: the third says so in plain words" (contains (simple 3) "Winnow keeps losing its connection to Bitcoin peers.")
  t.check "Advanced mode: every error shows" (contains (advanced 1) dropped)
  t.check "Advanced: never fully checked" (contains (advanced 0) "Chain not fully checked yet")
  let st : Status := { lastCheckedAgo := some (relativeAgo 300) }
  let mm : Model := { stage := .ready, settings := { advancedMode := true }, status := st, backgroundRefreshAvailable := false }
  let checked := (ElmLean.Html.toWire (.list (walletSections mm) : H)).toJson.compress
  t.check "Advanced: last checked" (contains checked "Chain last checked 5 min ago")
  t.check "Advanced: Background App Refresh off" (contains checked "Background App Refresh is off, so Winnow checks the chain only while open.")
  t.check "relative: under a minute" (relativeAgo 59 == "under a minute")
  t.check "relative: hours and minutes" (relativeAgo (2 * 3600 + 3 * 60) == "2 hr, 3 min")
  t.check "relative: days" (relativeAgo (3 * 86400 + 4 * 3600) == "3 days, 4 hr" && relativeAgo 86400 == "1 day")

/-! ## Background checks (upstream d2ca878 `BackgroundSyncTests`) -/

/-- Waits (up to `ms`) for `cond`. -/
def waitFor (ms : Nat) (cond : IO Bool) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  repeat
    if ← cond then return true
    if (← IO.monoMsNow) ≥ deadline then return false
    IO.sleep 5
  return false

/-- Sleeps `ms` unless the task is cancelled first (`Task.sleep` throwing `CancellationError`). -/
def cancellableSleep (ms : Nat) : IO Unit := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if ← IO.checkCanceled then return
    IO.sleep 5

def backgroundRuns (t : T) : IO Unit := do
  -- testCompletionOccursOnceAndCancelsDeadline
  let completions ← IO.mkRef (#[] : Array Bool)
  let cancellations ← IO.mkRef 0
  let run ← Real.BackgroundSyncRun.new 20 (pure true) (cancellations.modify (· + 1)) fun ok => completions.modify (·.push ok)
  run.start; run.start
  discard <| waitFor 1000 do return !(← completions.get).isEmpty
  run.expire
  IO.sleep 40
  t.check "background run: completes once, successfully" ((← completions.get) == #[true] && (← cancellations.get) == 0)
  -- testExpirationDrainsWorkAndCannotReportSuccess
  let completions ← IO.mkRef (#[] : Array Bool)
  let cancellations ← IO.mkRef 0
  let started ← IO.mkRef false
  let drained ← IO.mkRef false
  let drainedAtCompletion ← IO.mkRef false
  let run ← Real.BackgroundSyncRun.new 10_000 (do started.set true; cancellableSleep 10_000; drained.set true; return true)
    (cancellations.modify (· + 1)) fun ok => do drainedAtCompletion.set (← drained.get); completions.modify (·.push ok)
  run.start
  discard <| waitFor 1000 started.get
  run.expire; run.expire
  discard <| waitFor 1000 do return !(← completions.get).isEmpty
  IO.sleep 20
  t.check "background run: an expired run drains, then fails once" ((← completions.get) == #[false] && (← drainedAtCompletion.get))
  t.check "background run: one cancellation" ((← cancellations.get) == 1)
  -- testDeadlineCancelsHungWork
  let completions ← IO.mkRef (#[] : Array Bool)
  let run ← Real.BackgroundSyncRun.new 10 (do cancellableSleep 10_000; return true) (pure ()) fun ok => completions.modify (·.push ok)
  run.start
  t.check "background run: the deadline cancels hung work" (← waitFor 1000 do return (← completions.get) == #[false])
  -- testBackgroundAndForegroundCannotOwnNetworkingTogether
  let env ← gatewayEnv none
  env.modify fun c => { c with active := true }
  t.check "background: refused while the scene is active" (!(← Real.runBackgroundSync env {}) && !(← env.get).backgroundRunning)
  -- testColdBackgroundRunOpensTheWalletScansAndTearsDown (a custom signet, an unreachable peer)
  let vars := [("WINNOW_E2E", "1"), ("WINNOW_E2E_RUN", "background"), ("WINNOW_E2E_ENTROPY", "000102030405060708090a0b0c0d0e0f"),
               ("WINNOW_E2E_PEER", "127.0.0.1:1"), ("WINNOW_E2E_CHALLENGE", "51")]
  match WinnowApp.E2E.resolve (fun k => vars.lookup k) with
  | .active mode =>
    let root ← IO.FS.createTempDir
    let dir := (root / "signet").toString
    IO.FS.createDirAll dir
    let ks := Winnow.inMemoryKeyStore (← IO.mkRef {})
    discard <| (Wallet.create .signet ks (some (System.FilePath.mk dir / "wallet.json")) mode.entropy).run
    let env ← Real.Env.new { keyStore := ks, fetch := fun _ => throw (.other "offline"), networkParams := mode.networkParams, peerCount := 1 }
    let booted ← Real.openWallet env .signet dir
    t.check "cold background run: boot opens the wallet without networking" ((booted matches .opened _) && (← env.get).stack.isNone)
    let settings : Settings := { network := .signet, signet := { manualPeers := ["127.0.0.1:1"] } }
    let complete ← Real.runBackgroundSync env settings
    let c ← env.get
    t.check "cold background run: an unreachable peer cannot finish a check" (!complete)
    t.check "cold background run: no networking left running" (c.stack.isNone && !c.backgroundRunning && !c.active)
    t.check "cold background run: never fully checked" c.lastCompleteCheck.isNone
    Real.startNetworking env settings
    t.check "cold background run: the foreground still starts normally" ((← env.get).stack.bind (·.filters)).isSome
    Real.stopNetworking env
    IO.FS.removeDirAll root
  | _ => t.check "cold background run: test mode resolves" false
  -- testBackgroundIdentifiersAreDeclaredInBuiltApplication: the Info.plist the app's manifest generates
  let info := WinnowApp.manifest.infoPlist
  let strs (k : String) : List String := match info.getObjValAs? (Array String) k with
    | .ok a => a.toList
    | .error _ => []
  t.check "background: the identifiers are permitted in Info.plist"
    (strs "BGTaskSchedulerPermittedIdentifiers" == [Real.backgroundRefreshID, Real.backgroundProcessingID])
  t.check "background: fetch and processing modes" (strs "UIBackgroundModes" == ["fetch", "processing"])
  t.check "background: the manifest passes LeanNative's capability checks" WinnowApp.manifest.problems.isEmpty
  -- the Model: a cold launch's task waits for boot, boot without a scene starts no networking
  let (m, cs) := onHost (.bgtask Real.backgroundRefreshID "refresh") ({} : Model)
  t.check "Model: a task launched during boot waits for the wallet" (m.pendingBackgroundTask == some (Real.backgroundRefreshID, "refresh") &&
    cs.any (· matches .scheduleBackgroundTasks) && !cs.any (· matches .runBackgroundTask ..))
  let (m, cs) := onHost (.booted 0 (.opened "w")) m
  t.check "Model: boot runs it, without foreground networking" (cs.any (· matches .runBackgroundTask ..) &&
    !cs.any (· matches .startNetworking ..) && m.pendingBackgroundTask.isNone)
  let (m, cs) := onHost (.scene true) m
  t.check "Model: the scene becoming active starts networking" (cs.any (· matches .startNetworking ..) && m.active)
  let (_, cs) := onHost (.scene false) m
  t.check "Model: backgrounding asks for the next checks" (cs.any (· matches .scheduleBackgroundTasks) && cs.any (· matches .stopNetworking))
  let (_, cs) := onHost (.bgtaskExpired Real.backgroundRefreshID "refresh") m
  t.check "Model: an expired task is cancelled" (cs.any (· matches .expireBackgroundTask _))
  t.check "system events: a launched task" ((system (Lean.Json.mkObj [("bgtask", Lean.Json.mkObj [("id", "x"), ("kind", "processing")])])) matches some (.bgtask "x" "processing"))
  t.check "system events: an expired task" ((system (Lean.Json.mkObj [("bgtaskExpired", Lean.Json.mkObj [("id", "x"), ("kind", "refresh")])])) matches some (.bgtaskExpired "x" "refresh"))

def main : IO UInt32 := do
  let t : T := { passed := ← IO.mkRef 0, failed := ← IO.mkRef #[] }
  let root ← IO.FS.createTempDir
  IO.println s!"records-test in {root}"
  syncErrorBookkeeping t
  peerGatewayModel t
  syncBookkeepingScreens t
  backgroundRuns t
  try
    let a ← newPhone root "A"
    let b ← newPhone root "B"
    peopleAndPastes t a b
    receiveLabels t a b
    lookupSenderTest t b
    let before ← a.records
    tamper t root a
    reopenFromDisk t a before
  catch e =>
    t.check "the script ran to the end" false (toString e)
  let failed ← t.failed.get
  IO.println s!"records-test: {← t.passed.get} passed, {failed.size} failed"
  return if failed.isEmpty then 0 else 1
