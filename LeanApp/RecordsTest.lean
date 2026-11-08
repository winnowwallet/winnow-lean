import WinnowApp.Real.RecordsBackend
import WinnowApp.Real
import WinnowApp.View
import WinnowApp.E2E
import WinnowApp.Project
import WinnowApp.Main
import LeanNative.Erase
import LeanNative.Json
import TestKit.Check
import TestKit.Regtest
import FoundationVectors

/-! `records-test`: a scripted run of every records operation against a temporary directory, with the
in-memory key store and two wallets made by `Wallet.create` (two phones: A and B).

Covers people (add, rename, label, attach, remove), every kind of paste, receive and sender labels, store
tamper detection (on the sealed people file), a wrong-network store, a first write that fails, and
reopening everything from disk; the People store's payment index and pay-to checks; and the screens the
journeys open but never use (Home's payment screen, People, Settings, Receive, the recovery phrase and the
backup file with Simple mode's Back up page and Restore from a file, and `Model.fail` for every failure a
screen can get), driven as a person uses them through the app's own `perform`; background tasks launched and
expired through `perform` (`backgroundTaskCommands`), and test mode's one seed variable. Exits 1 on any
failure. (The shared-savings and MuSig2 scenarios went with vaults, upstream 1cf93fb; cards and records
written with a `signerKey` still read.) -/

open Winnow WinnowApp WinnowApp.RecordsReal TestKit
open TestKit.Regtest (waitUntil)
open Tx (BitcoinNetwork)

instance : Describe RecordsError := ⟨(·.name), fun e => s!"{e.name}: {e.description}"⟩

/-- Runs `x`, a check that it succeeds; the value, or `none`. -/
def succeeds {α} (name : String) (x : RM α) : IO (Option α) := do
  match ← x.run with
  | .ok a => check name true; return some a
  | .error e => check name false s!"{e.name}: {e.description}"; return none

/-- `succeeds`, and the script stops when it does not. -/
def obtain {α} (name : String) (x : RM α) : IO α := do
  match ← succeeds name x with
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

def peopleAndPastes (a b : Phone) : IO Unit := do
  -- cards and own keys
  let cardB ← obtain "ownCard B" (do return (← ownPersonCard b.wallet "Bob").serialized)
  let keyB ← obtain "ownKeyExpression B" (ownKeyExpression b.wallet false)
  let keyBm ← obtain "ownKeyExpression B multipath" (ownKeyExpression b.wallet true)
  check "own key expression shape" (keyB.startsWith "[" && (keyB.splitOn "/86'/1'/0']tpub").length == 2 && keyBm == keyB ++ "/<0;1>/*") keyB
  -- pastes of each kind
  let pCard ← obtain "paste card" (parsePaste network cardB)
  check "paste card reads name and fresh pay-to" (pCard.name == some "Bob" && pCard.payTo == some true)
  let pKey ← obtain "paste key expression" (parsePaste network keyB)
  check "paste bare key: fresh pay-to" (pKey.payTo == some true && pKey.name.isNone)
  let pKeyM ← obtain "paste multipath key" (parsePaste network keyBm)
  check "paste multipath key" (pKeyM.payTo == some true)
  let pDesc ← obtain "paste descriptor" (parsePaste network s!"tr({keyBm})")
  check "paste descriptor: pay-to" (pDesc.payTo == some true)
  let addrB ← obtain "B address" (wm (b.wallet.address .receive 7))
  let pAddr ← obtain "paste address" (parsePaste network addrB)
  check "paste address: one address" (pAddr.payTo == some false)
  refused "paste empty" (kind := "empty") (parsePaste network "   ")
  refused "paste garbage" (kind := "unrecognised") (parsePaste network "hello world")
  refused "paste mainnet address on regtest" (kind := "wrongNetwork") (parsePaste network "bc1qar0srrr7xfkvy5l643lydnw9re59gtzzwf5mdq")
  let otherNet ← obtain "card for another network" (do
    let c := PersonCard.make .mainnet "Eve" none
    return c.serialized)
  refused "paste card of another network" (kind := "wrongNetwork") (parsePaste network otherNet)
  -- a card from a Winnow that also shared a signer key still reads; the key is ignored
  let oldCard := s!"\{\"name\":\"Bob\",\"network\":\"regtest\",\"payTo\":\"tr({keyBm})\",\"signerKey\":\"{keyBm}\",\"version\":1,\"winnow\":\"person-card\"}"
  let pOld ← obtain "paste a card that carries a signer key" (parsePaste network oldCard)
  check "the old card reads as a pay-to card" (pOld.name == some "Bob" && pOld.payTo == some true)
  check "a stored person's signerKey is ignored, and never written back"
    (match SwiftJSON.decodeText s!"\{\"id\":\"p\",\"name\":\"Old\",\"nextPaymentIndex\":0,\"signerKey\":\"{keyBm}\"}" PersonRecord.ofJV with
     | .ok r => r.payTo.isNone && SwiftJSON.write r.toJV == "{\"id\":\"p\",\"name\":\"Old\",\"nextPaymentIndex\":0}"
     | .error _ => false)
  -- add / rename / duplicates
  let r ← obtain "add Bob from card" (addPerson a.store (some a.wallet) "Bob" (some cardB) none none none)
  let some bob := r.people.find? (·.name == "Bob") | check "Bob saved" false; return
  check "Bob is paid at fresh addresses" (bob.payTo == some true)
  check "recipientByScript covers Bob's first scripts" ((r.recipientByScript.filter (·.2 == bob.id)).length == 20)
  refused "duplicate card refused" (kind := "duplicate") (addPerson a.store (some a.wallet) "Bobby" (some cardB) none none none)
  refused "a name over two lines is refused" (kind := "invalidState") (addPerson a.store (some a.wallet) "Bo\nb" (some addrB) none none none)
  let r ← obtain "rename Bob" (updateRecipient a.store (some a.wallet) bob.id (some "Robert") true)
  check "renamed" ((r.people.find? (·.id == bob.id)).map (·.name) == some "Robert")
  let r ← obtain "add Carol from an address" (addPerson a.store (some a.wallet) "Carol" (some addrB) none none none)
  let some carol := r.people.find? (·.name == "Carol") | check "Carol saved" false; return
  check "Carol pays one address" (carol.payTo == some false)
  -- sender labels
  let txid := hex (ByteArray.mk (Array.replicate 32 0x5a))
  let r ← obtain "add Dave as the sender of a payment" (addPerson a.store (some a.wallet) "Dave" none none none (some txid))
  let some dave := r.people.find? (·.name == "Dave") | check "Dave saved" false; return
  check "Dave is name-only and labels the payment" (dave.payTo.isNone && r.senderByTxid == [(txid, dave.id)])
  refused "label with an unknown person" (kind := "unknownPerson") (labelSender a.store (some a.wallet) txid "nobody")
  refused "label with an invalid txid" (kind := "invalidState") (labelSender a.store (some a.wallet) "abcd" dave.id)
  refused "a sender with an invalid txid" (kind := "invalidState") (addPerson a.store (some a.wallet) "Eve" none none none (some "abcd"))
  let r ← RM.toIO (RM.io (RecordsReal.records a.store (some a.wallet)))
  check "the person is saved even when the label is refused (as AppModel's two steps)" (r.people.any (·.name == "Eve"))
  let some eve := r.people.find? (·.name == "Eve") | check "Eve saved" false; return
  let aR ← a.reopen
  check "and disk agrees with memory" ((← RecordsReal.records aR.store (some a.wallet)).people.any (·.name == "Eve"))
  discard <| obtain "remove Eve" (removePerson a.store (some a.wallet) eve.id)
  let addrB2 ← obtain "B address 8" (wm (b.wallet.address .receive 8))
  let r ← obtain "attach a funding address to Dave" (attachDestination a.store (some a.wallet) dave.id addrB2 .localFunding (some txid))
  check "Dave now has an unverified funding destination"
    (((r.people.find? (·.id == dave.id)).map fun p => p.payTo == some false && p.provenance == some .localFunding) == some true)
  refused "a second destination is refused" (kind := "invalidState") (attachDestination a.store (some a.wallet) dave.id addrB .supplied none)
  let r ← obtain "remove the sender label" (removeSenderLabel a.store (some a.wallet) txid)
  check "label removed" r.senderByTxid.isEmpty
  discard <| obtain "label again" (labelSender a.store (some a.wallet) txid dave.id)
  let r ← obtain "remove Dave" (removePerson a.store (some a.wallet) dave.id)
  check "removing a person prunes their labels" (r.senderByTxid.isEmpty && !(r.people.any (·.id == dave.id)))
  let r ← obtain "remove Carol" (removePerson a.store (some a.wallet) carol.id)
  check "Carol removed" (!(r.people.any (·.id == carol.id)))
  refused "remove twice" (kind := "unknownPerson") (removePerson a.store (some a.wallet) carol.id)
  -- hide and re-save a recipient keeps the record
  let r ← obtain "hide Robert" (updateRecipient a.store (some a.wallet) bob.id none false)
  check "hidden" (((r.people.find? (·.id == bob.id)).map (·.isSavedRecipient)) == some false)
  let r ← obtain "re-saving the hidden card restores it" (addPerson a.store (some a.wallet) "Bob" (some cardB) none none none)
  check "same record, saved again, renamed" (((r.people.find? (·.id == bob.id)).map fun p => p.isSavedRecipient && p.name == "Bob") == some true)
  -- B knows A too
  let cardA ← obtain "ownCard A" (do return (← ownPersonCard a.wallet "Alice").serialized)
  discard <| obtain "B adds Alice" (addPerson b.store (some b.wallet) "Alice" (some cardA) none none none)

def receiveLabels (a b : Phone) : IO Unit := do
  let addr ← obtain "A receive address" (wm (a.wallet.address .receive 0))
  let foreign ← obtain "B receive address" (wm (b.wallet.address .receive 0))
  let r ← obtain "set a receive label" (setReceiveLabel a.store a.wallet addr "Invoice 12")
  check "label shown by address" (r.receiveLabels == [(addr, "Invoice 12")])
  refused "a label for someone else's address is refused" (kind := "noWallet")
    (setReceiveLabel a.store a.wallet foreign "x")
  refused "a two-line label is refused" (kind := "invalidLabel") (setReceiveLabel a.store a.wallet addr "a\nb")
  let addr1 ← obtain "A receive address 1" (wm (a.wallet.address .receive 1))
  discard <| obtain "second label" (setReceiveLabel a.store a.wallet addr1 "  Rent  ")
  let r ← obtain "empty text removes a label" (setReceiveLabel a.store a.wallet addr "")
  check "one label left, trimmed" (r.receiveLabels == [(addr1, "Rent")])
  let file ← IO.FS.readFile (a.dir / "receive-labels.json")
  let script ← obtain "script of address 1" (RM.lift (fun e => namedError e.name network) (AddressDecoder.scriptPubKey addr1 network))
  check "labels file in the Swift shape"
    (file == s!"\{\"labels\":\{\"{hex script}\":\"Rent\"},\"network\":\"regtest\",\"version\":1,\"walletID\":\"{a.wallet.id}\"}") file

def lookupSenderTest (b : Phone) : IO Unit := do
  let txid := hex (ByteArray.mk (Array.replicate 32 0x11))
  let funder ← obtain "B address 9" (wm (b.wallet.address .receive 9))
  let answer := s!"\{\"txid\":\"{txid}\",\"vin\":[\{\"prevout\":\{\"scriptpubkey_address\":\"{funder}\"}},\{\"prevout\":null},\{\"prevout\":\{\"scriptpubkey_address\":\"{funder}\"}}]}"
  let urls ← IO.mkRef ([] : List String)
  let get : String → Nat → IO ByteArray := fun url _ => do urls.modify (url :: ·); return answer.toUTF8
  let addrs ← obtain "lookupSender" (lookupSender get network txid "https://example.org/api/")
  check "distinct funding addresses, in input order" (addrs == [funder])
  check "GET {base}/tx/{txid}" ((← urls.get) == [s!"https://example.org/api/tx/{txid}"])
  let other : String → Nat → IO ByteArray := fun _ _ => return "{\"txid\":\"00\",\"vin\":[]}".toUTF8
  refused "a different transaction is refused" (kind := "unavailable") (lookupSender other network txid "https://example.org/api")
  let bad : String → Nat → IO ByteArray := fun _ _ => return "[]".toUTF8
  refused "a wrong shape is refused" (kind := "unavailable") (lookupSender bad network txid "https://example.org/api")
  refused "an invalid txid is refused" (kind := "unavailable") (lookupSender get network "abc" "https://example.org/api")

def tamper (root : System.FilePath) (a : Phone) : IO Unit := do
  -- tampered people.json: a notice, and every mutation refused
  let peoplePath := a.dir / "people.json"
  let good ← IO.FS.readBinFile peoplePath
  check "people.json is sealed" (SealedStoreFile.isSealed good)
  IO.FS.writeBinFile peoplePath (mutateByte good (good.size - 3))
  let a2 ← a.reopen
  let r ← a2.records
  check "tampered people: unverified notice, no people"
    (r.peopleStorageNotice == some PeopleStore.unverifiedStorageMessage && r.people.isEmpty)
  refused "a damaged people store refuses mutations" (kind := "damaged")
    (addPerson a2.store (some a.wallet) "Zed" none none none (some (hex (ByteArray.mk (Array.replicate 32 1)))))
  IO.FS.writeBinFile peoplePath good
  -- unsealed file while a key exists
  match SealedStoreFile.open good "people" network ((← (a.keys.key "people.regtest").run).toOption.join.getD .empty) with
  | .ok payload =>
    IO.FS.writeBinFile peoplePath payload
    let a3 ← a.reopen
    check "an unsealed file once a key exists reads as unverified"
      ((← a3.records).peopleStorageNotice == some PeopleStore.unverifiedStorageMessage)
    -- a valid seal around invalid content is damage, not substitution
    let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
    IO.FS.writeBinFile peoplePath (SealedStoreFile.sealed "{\"people\":[{\"id\":\"x\"}]}".toUTF8 "people" network key)
    let a4 ← a.reopen
    check "valid seal, invalid records: the damaged message"
      ((← a4.records).peopleStorageNotice == some PeopleStore.damagedStorageMessage)
  | .error e => check "own people file opens" false e.name
  IO.FS.writeBinFile peoplePath good
  let unverified (st : RecordsStore) : IO Bool := do
    return (← RecordsReal.records st none).peopleStorageNotice == some PeopleStore.unverifiedStorageMessage
  let peopleKey := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  -- a file sealed for another store name (the seal binds the store)
  match SealedStoreFile.open good "people" network peopleKey with
  | .ok payload =>
    IO.FS.writeBinFile peoplePath (SealedStoreFile.sealed payload "vaults" network peopleKey)
    check "a file sealed for another store is refused" (← unverified (← a.reopen).store)
  | .error e => check "own people file opens" false e.name
  IO.FS.writeBinFile peoplePath good
  -- wrong network, same device: a regtest file under signet, where signet has a key
  let sigDir := root / "A-signet"
  IO.FS.createDirAll sigDir
  let sig ← RecordsStore.open .signet (some sigDir) a.keys
  discard <| obtain "signet store's first write establishes its key"
    (addPerson sig none "Sam" none none none (some (hex (ByteArray.mk (Array.replicate 32 2)))))
  IO.FS.writeBinFile (sigDir / "people.json") good
  check "a regtest people file under signet fails verification" (← unverified (← RecordsStore.open .signet (some sigDir) a.keys))
  -- wrong network, fresh device: sealed file, no key at all
  let fresh ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let freshDir := root / "fresh"
  IO.FS.createDirAll freshDir
  IO.FS.writeBinFile (freshDir / "people.json") good
  check "a sealed file without its key is refused (keyMissing)"
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
    check "an unsealed legacy file loads" r.peopleStorageNotice.isNone
    check "and is sealed now" (SealedStoreFile.isSealed (← IO.FS.readBinFile (legacyDir / "people.json")))
    check "with its people" (!r.people.isEmpty)
  | .error e => check "own people file opens" false e.name
  -- a first write that fails discards the new key
  let failKeys ← IO.mkRef ({} : Std.HashMap String ByteArray)
  let failDir := root / "fail"
  IO.FS.createDirAll failDir
  let fs ← RecordsStore.open network (some failDir) (StoreKeyVault.inMemory failKeys)
    (writeData := fun _ _ => throw (IO.userError "disk full"))
  refused "a failed first write fails" (kind := "ioError")
    (addPerson fs none "Nia" none none none (some (hex (ByteArray.mk (Array.replicate 32 3)))))
  check "and leaves no key behind" (!(← failKeys.get).contains "people.regtest")
  check "and no person" (← records fs none).people.isEmpty
  -- a damaged label file: a notice, sets refused
  let labelsPath := a.dir / "receive-labels.json"
  let lgood ← IO.FS.readBinFile labelsPath
  IO.FS.writeBinFile labelsPath "{\"version\":2}".toUTF8
  let a5 ← a.reopen
  let r ← a5.records
  check "damaged labels: notice" (r.receiveLabelStorageNotice == some (RecordsError.labels .damaged).description && r.receiveLabels.isEmpty)
  let addr ← obtain "address" (wm (a.wallet.address .receive 2))
  refused "a damaged label store refuses sets" (kind := "damaged") (setReceiveLabel a5.store a.wallet addr "x")
  IO.FS.writeBinFile labelsPath lgood

def reopenFromDisk (a : Phone) (before : Records) : IO Unit := do
  let a2 ← a.reopen
  let r ← a2.records
  check "reopen: the same people" (r.people == before.people) s!"{reprStr r.people}"
  check "reopen: the same labels" (r.receiveLabels == before.receiveLabels && r.senderByTxid == before.senderByTxid)
  check "reopen: no notices" (r.peopleStorageNotice.isNone && r.receiveLabelStorageNotice.isNone)
  -- the people file is exactly what the Swift encoder writes for these records
  let st ← a2.store.read
  let file ← IO.FS.readBinFile (a.dir / "people.json")
  let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  check "people.json: seal over the sorted-key envelope"
    (file == SealedStoreFile.sealed (PeopleStore.encode st.people.records st.people.senderByTxid) "people" network key)

/-- Upstream d2ca878's `BackgroundSyncTests`: Simple mode waits out dropped peers but shows other errors at
once, and only link failures count as transient. -/
def syncErrorBookkeeping : IO Unit := do
  let dropped := (Winnow.IO.NetError.peer (.disconnected "closed")).description
  check "simple sync error: none without an error" (simpleSyncError none none 0 == none)
  check "simple sync error: one dropped peer stays quiet" (simpleSyncError (some dropped) (some dropped) 1 == none)
  check "simple sync error: two dropped peers stay quiet" (simpleSyncError (some dropped) (some dropped) 2 == none)
  check "simple sync error: a third is said in plain words" (simpleSyncError (some dropped) (some dropped) 3 ==
    some "Winnow keeps losing its connection to Bitcoin peers. It will keep trying.")
  let mismatch := (Winnow.IO.NetError.filters (.filterHeaderMismatch 7)).description
  check "simple sync error: another failure shows as is" (simpleSyncError (some mismatch) (some dropped) 1 == some mismatch)
  check "simple sync error: a lone failure shows as is" (simpleSyncError (some mismatch) none 0 == some mismatch)
  check "transient: a dropped peer" (isTransientSyncError (.peer (.disconnected "closed")))
  check "transient: a timeout" (isTransientSyncError (.peer .timeout))
  check "transient: peers cooling down" (isTransientSyncError (.filters (.peersCoolingDown 2)))
  check "transient: no peers" (isTransientSyncError (.filters .noPeers))
  check "not transient: a protocol violation" (!isTransientSyncError (.peer (.protocolViolation "bad")))
  check "not transient: a checkpoint mismatch" (!isTransientSyncError (.filters (.checkpointMismatch "split")))
  check "not transient: a corrupt file" (!isTransientSyncError (.other "The file couldn’t be opened because it isn’t in the correct format."))

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
def peerGatewayModel : IO Unit := do
  -- testAutomaticDefaultAndManualOverridePersistAcrossModes
  let m : Model := { stage := .ready, settings := { advancedMode := true } }
  check "gateways: Automatic by default" (m.settings.peerGatewaySettings.mode == "automatic" && (relaunch {}).peerGatewaySettings == {})
  let m := m.loadGatewayDraft
  let config : PeerGatewayConfiguration := { networks := [.i2p], i2pProxy := some { host := "gateway", port := 4447 } }
  let m := (stepSettings (.setGatewayMode 2) m).1
  let m := (stepSettings (.setGatewayNetwork .clearnet false) m).1
  let m := (stepSettings (.setGatewayNetwork .i2p true) m).1
  let m := (stepSettings (.setI2PAddress "gateway:4447") m).1
  let (m, cs) := stepSettings .applyGateways m
  check "gateways: Apply saves the manual gateways" (m.settings.peerGatewaySettings == { mode := "manual", manual := config })
    (reprStr m.settings.peerGatewaySettings)
  check "gateways: Apply saves and reconnects" (cs.length == 2 && cs.any (· matches .reconnect ..) && cs.any (· matches .saveSettings _))
  let m := (step (.setAdvanced false) m).1
  let relaunched := relaunch m.settings
  check "gateways: the manual override survives Simple mode and a relaunch" (relaunched.peerGatewaySettings == { mode := "manual", manual := config })
  let http ← RoutedHTTPClient.ofGateways (fun _ => throw (.other "offline")) relaunched.peerGatewaySettings.initialActive
  check "gateways: I2P alone makes no HTTP request" (!http.enabled)
  let m := { m with settings := { m.settings with advancedMode := true } }.loadGatewayDraft
  let m := (stepSettings (.setGatewayNetwork .i2p false) m).1
  let (bad, badCmds) := stepSettings .applyGateways m
  check "gateways: an invalid edit does not overwrite the settings"
    (bad.settings.peerGatewaySettings.manual == config && badCmds.isEmpty &&
     bad.settingsDraft.gatewayError == some PeerGatewayConfiguration.Invalid.configuration.description)
  let (typo, _) := stepSettings .applyGateways (stepSettings (.setI2PAddress "gateway") (stepSettings (.setGatewayNetwork .i2p true) m).1).1
  check "gateways: an incomplete address is refused" (typo.settingsDraft.gatewayError == some PeerGatewayConfiguration.Invalid.address.description &&
    typo.settings.peerGatewaySettings.manual == config)
  let (direct, _) := stepSettings .applyGateways (stepSettings (.setGatewayMode 1) m).1
  check "gateways: Direct only persists" ((relaunch direct.settings).peerGatewaySettings.mode == "direct")
  check "gateways: Direct only keeps the manual gateways for later" ((relaunch direct.settings).peerGatewaySettings.manual == config)
  -- testRoutingBannerSaysWhetherPeersSeeTheIPAddress
  let tor : Winnow.Net.PeerEndpoint := { host := "100.75.175.127", port := 9050 }
  let i2p : Winnow.Net.PeerEndpoint := { host := "100.74.30.8", port := 4447 }
  let state (mode : String) (c : PeerGatewayConfiguration) (discovering := false) := PeerRoutingState.current mode c discovering
  check "banner: Tor and I2P" (state "automatic" { networks := [.tor, .i2p], torProxy := some tor, i2pProxy := some i2p } == .overlay true true)
  check "banner: Tor" (state "automatic" { networks := [.tor], torProxy := some tor } == .overlay true false)
  check "banner: Automatic found nothing" (state "automatic" {} == .direct true)
  check "banner: Direct only" (state "direct" {} == .direct false)
  check "banner: mixed" (state "manual" { networks := [.clearnet, .i2p], i2pProxy := some i2p } == .mixed)
  check "banner: checking" (state "automatic" {} true == .checking)
  check "banner: offline" (state "manual" { networks := [] } == .offline)
  check "banner: the private line" ((PeerRoutingState.overlay true true).message == "Private: peers reached through Tor and I2P")
  check "banner: a fallback says the IP is seen" (contains (PeerRoutingState.direct true).message "can see your IP address")
  check "banner: mixed says the IP is seen" (contains PeerRoutingState.mixed.message "can see your IP address")
  let banner := (LeanNative.Html.toWire (.list (beginnerSections { m with settings := { network := .mainnet } }) : H)).toJson.compress
  check "banner: Simple mode shows it on mainnet" (contains banner "peerRoutingBanner" && contains banner "Direct: peers can see your IP address. No Tor")
  let signet := (LeanNative.Html.toWire (.list (beginnerSections { m with settings := { network := .signet } }) : H)).toJson.compress
  check "banner: not on signet" (!contains signet "peerRoutingBanner")
  -- testCandidateCountFollowsRoutedNetworks
  let entry : CensusEntry := { host := "8.8.8.8", port := 8333, userAgent := "/Satoshi:30/", startHeight := 900_000 }
  let nets := #[("clearnet", #[entry, entry]), ("tor", #[entry]), ("i2p", #[entry, entry, entry])]
  let catalog : CensusCatalog := { date := "2026-09-28", tip := 900_000, networks := nets }
  check "candidates: clearnet" (Real.candidateCount catalog == "2 candidates")
  check "candidates: I2P" (Real.candidateCount catalog [.i2p] == "3 candidates")
  check "candidates: Tor" (Real.candidateCount catalog [.tor] == "1 candidate")
  check "candidates: all three" (Real.candidateCount catalog [.clearnet, .tor, .i2p] == "6 candidates")
  -- testCorruptSavedSettingsStayOffline
  let corrupt : Settings := match Lean.Json.parse "{\"peerGatewaySettings\":\"broken\"}" >>= Lean.fromJson? with
    | .ok s => s | .error _ => {}
  check "corrupt settings: read as offline" (corrupt.peerGatewaySettings == PeerGatewaySettings.unreadable)
  let env ← gatewayEnv (some (pure discoveredTor))
  env.modify (·.withSettings corrupt)
  Real.preparePeerGateways env
  let c ← env.get
  check "corrupt settings: networking stays offline" (!c.activeGateways.isValid && !c.http.enabled)
  -- testDiscoveredAddressesAreNotPersisted
  let env ← gatewayEnv (some (pure discoveredTor))
  let saved : Settings := {}
  env.modify (·.withSettings saved)
  Real.preparePeerGateways env
  let c ← env.get
  check "discovery: the gateways found are in use" (c.activeGateways == discoveredTor && c.http.proxy == discoveredTor.torProxy)
  check "discovery: nothing is persisted" (!contains (Lean.toJson saved).compress "100.75.175.127")
  let fresh ← gatewayEnv none
  check "discovery: a relaunch starts from clearnet" ((← fresh.get).activeGateways == {})
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
  check "discovery: Checking while it runs" (← env.get).discoveringGateways
  (← gate.get).resolve discoveredTor
  discard <| IO.wait first
  discard <| IO.wait second
  Real.preparePeerGateways env
  check "discovery: one discovery for every caller of a generation" ((← asked.get) == 1 && (← env.get).activeGateways == discoveredTor)
  check "discovery: done" (!(← env.get).discoveringGateways)
  gate.set (← IO.Promise.new)
  Real.stopNetworking env
  let next ← IO.asTask (Real.preparePeerGateways env)
  while (← asked.get) < 2 do IO.sleep 5
  (← gate.get).resolve {}
  discard <| IO.wait next
  check "discovery: the next generation asks again" ((← asked.get) == 2 && (← env.get).activeGateways == {})
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
    check s!"stale discovery is dropped ({if changeMode then "mode change" else "background"})"
      (c.activeGateways == {} && !c.discoveringGateways)
  -- AppModel.backgroundRoutingAllowed (BackgroundSyncTests)
  let torGw : Winnow.Net.PeerEndpoint := { host := "100.64.0.1", port := 9050 }
  let i2pGw : Winnow.Net.PeerEndpoint := { host := "100.64.0.2", port := 4447 }
  let overlay : PeerGatewayConfiguration := { networks := [.tor, .i2p], torProxy := some torGw, i2pProxy := some i2pGw }
  check "background: no direct connection after the foreground used gateways" (!backgroundRoutingAllowed "automatic" {} true)
  check "background: through the gateways found" (backgroundRoutingAllowed "automatic" overlay true)
  check "background: direct when the foreground was direct too" (backgroundRoutingAllowed "automatic" {} false)
  check "background: Direct only as chosen" (backgroundRoutingAllowed "direct" {} true)
  check "background: Manual as chosen" (backgroundRoutingAllowed "manual" overlay true)

/-- Sync bookkeeping as the screens show it (upstream 66c6a48): Simple mode waits out dropped peers, Advanced
shows every error; Advanced's Sync section says when the chain was last checked. -/
def syncBookkeepingScreens : IO Unit := do
  let dropped := (Winnow.IO.NetError.peer (.disconnected "closed")).description
  let status (n : Nat) : Status := { lastSyncError := some dropped, transientSyncError := some dropped, transientSyncFailures := n }
  let simple (n : Nat) := (LeanNative.Html.toWire (.list (beginnerSections { stage := .ready, status := status n }) : H)).toJson.compress
  let advanced (n : Nat) := (LeanNative.Html.toWire (.list (walletSections { stage := .ready, settings := { advancedMode := true }, status := status n }) : H)).toJson.compress
  check "Simple mode: a dropped peer stays quiet" (!contains (simple 1) "closed")
  check "Simple mode: the third says so in plain words" (contains (simple 3) "Winnow keeps losing its connection to Bitcoin peers.")
  check "Advanced mode: every error shows" (contains (advanced 1) dropped)
  check "Advanced: never fully checked" (contains (advanced 0) "Chain not fully checked yet")
  let st : Status := { lastCheckedAgo := some (relativeAgo 300) }
  let mm : Model := { stage := .ready, settings := { advancedMode := true }, status := st, backgroundRefreshAvailable := false }
  let checked := (LeanNative.Html.toWire (.list (walletSections mm) : H)).toJson.compress
  check "Advanced: last checked" (contains checked "Chain last checked 5 min ago")
  check "Advanced: Background App Refresh off" (contains checked "Background App Refresh is off, so Winnow checks the chain only while open.")
  check "relative: under a minute" (relativeAgo 59 == "under a minute")
  check "relative: hours and minutes" (relativeAgo (2 * 3600 + 3 * 60) == "2 hr, 3 min")
  check "relative: days" (relativeAgo (3 * 86400 + 4 * 3600) == "3 days, 4 hr" && relativeAgo 86400 == "1 day")

/-! ## Background checks (upstream d2ca878 `BackgroundSyncTests`) -/

/-- Sleeps `ms` unless the task is cancelled first (`Task.sleep` throwing `CancellationError`). -/
def cancellableSleep (ms : Nat) : IO Unit := do
  let deadline := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < deadline do
    if ← IO.checkCanceled then return
    IO.sleep 5

def backgroundRuns : IO Unit := do
  -- testCompletionOccursOnceAndCancelsDeadline
  let completions ← IO.mkRef (#[] : Array Bool)
  let cancellations ← IO.mkRef 0
  let run ← Real.BackgroundSyncRun.new 20 (pure true) (cancellations.modify (· + 1)) fun ok => completions.modify (·.push ok)
  run.start; run.start
  discard <| waitUntil 1000 (every := 5) do return !(← completions.get).isEmpty
  run.expire
  IO.sleep 40
  check "background run: completes once, successfully" ((← completions.get) == #[true] && (← cancellations.get) == 0)
  -- testExpirationDrainsWorkAndCannotReportSuccess
  let completions ← IO.mkRef (#[] : Array Bool)
  let cancellations ← IO.mkRef 0
  let started ← IO.mkRef false
  let drained ← IO.mkRef false
  let drainedAtCompletion ← IO.mkRef false
  let run ← Real.BackgroundSyncRun.new 10_000 (do started.set true; cancellableSleep 10_000; drained.set true; return true)
    (cancellations.modify (· + 1)) fun ok => do drainedAtCompletion.set (← drained.get); completions.modify (·.push ok)
  run.start
  discard <| waitUntil 1000 (every := 5) started.get
  run.expire; run.expire
  discard <| waitUntil 1000 (every := 5) do return !(← completions.get).isEmpty
  IO.sleep 20
  check "background run: an expired run drains, then fails once" ((← completions.get) == #[false] && (← drainedAtCompletion.get))
  check "background run: one cancellation" ((← cancellations.get) == 1)
  -- testDeadlineCancelsHungWork
  let completions ← IO.mkRef (#[] : Array Bool)
  let run ← Real.BackgroundSyncRun.new 10 (do cancellableSleep 10_000; return true) (pure ()) fun ok => completions.modify (·.push ok)
  run.start
  check "background run: the deadline cancels hung work" (← waitUntil 1000 (every := 5) do return (← completions.get) == #[false])
  -- testBackgroundAndForegroundCannotOwnNetworkingTogether
  let env ← gatewayEnv none
  env.modify fun c => { c with active := true }
  check "background: refused while the scene is active" (!(← Real.runBackgroundSync env {}) && !(← env.get).backgroundRunning)
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
    check "cold background run: boot opens the wallet without networking" ((booted matches .opened _) && (← env.get).stack.isNone)
    let settings : Settings := { network := .signet, signet := { manualPeers := ["127.0.0.1:1"] } }
    let complete ← Real.runBackgroundSync env settings
    let c ← env.get
    check "cold background run: an unreachable peer cannot finish a check" (!complete)
    check "cold background run: no networking left running" (c.stack.isNone && !c.backgroundRunning && !c.active)
    check "cold background run: never fully checked" c.lastCompleteCheck.isNone
    Real.startNetworking env settings
    check "cold background run: the foreground still starts normally" ((← env.get).stack.bind (·.filters)).isSome
    Real.stopNetworking env
    -- the loops see the stop at their next slice, and a pass still running saves the wallet into `root`
    check "cold background run: no loop thread outlives the stop"
      (← waitUntil 5_000 (every := 5) do return (← env.get).liveLoops == 0)
    IO.FS.removeDirAll root
  | _ => check "cold background run: test mode resolves" false
  -- testBackgroundIdentifiersAreDeclaredInBuiltApplication: the Info.plist the app's manifest generates
  let info := WinnowApp.manifest.infoPlist
  let strs (k : String) : List String := match info.getObjValAs? (Array String) k with
    | .ok a => a.toList
    | .error _ => []
  check "background: the identifiers are permitted in Info.plist"
    (strs "BGTaskSchedulerPermittedIdentifiers" == [Real.backgroundRefreshID, Real.backgroundProcessingID])
  check "background: fetch and processing modes" (strs "UIBackgroundModes" == ["fetch", "processing"])
  check "background: the manifest passes LeanNative's capability checks" WinnowApp.manifest.problems.isEmpty
  -- the Model: a cold launch's task waits for boot, boot without a scene starts no networking
  let (m, cs) := onHost (.bgtask Real.backgroundRefreshID "refresh") ({} : Model)
  check "Model: a task launched during boot waits for the wallet" (m.pendingBackgroundTask == some (Real.backgroundRefreshID, "refresh") &&
    cs.any (· matches .scheduleBackgroundTasks) && !cs.any (· matches .runBackgroundTask ..))
  let (m, cs) := onHost (.booted 0 (.opened "w")) m
  check "Model: boot runs it, without foreground networking" (cs.any (· matches .runBackgroundTask ..) &&
    !cs.any (· matches .startNetworking ..) && m.pendingBackgroundTask.isNone)
  let (m, cs) := onHost (.scene true) m
  check "Model: the scene becoming active starts networking" (cs.any (· matches .startNetworking ..) && m.active)
  let (_, cs) := onHost (.scene false) m
  check "Model: backgrounding asks for the next checks" (cs.any (· matches .scheduleBackgroundTasks) && cs.any (· matches .stopNetworking))
  let (_, cs) := onHost (.bgtaskExpired Real.backgroundRefreshID "refresh") m
  check "Model: an expired task is cancelled" (cs.any (· matches .expireBackgroundTask _))
  check "system events: a launched task" ((system (Lean.Json.mkObj [("bgtask", Lean.Json.mkObj [("id", "x"), ("kind", "processing")])])) matches some (.bgtask "x" "processing"))
  check "system events: an expired task" ((system (Lean.Json.mkObj [("bgtaskExpired", Lean.Json.mkObj [("id", "x"), ("kind", "refresh")])])) matches some (.bgtaskExpired "x" "refresh"))

/-! ## The screens, as a person uses them (#35, #44, #45, #48, #64)

Each flow sends the Model what a tap sends (`step`), runs the commands through the app's own `perform`
against a backend (the real one over a wallet opened from disk with no network, or a stub that records what
reaches it), hands every answer back through `onHost`, and reads the screen as the shell receives it. The
journeys open these screens; these flows use their controls. -/

/-- The shell's side of `perform`: the answers it posts, collected; `auth` and the other capabilities say yes,
`clipboard.get` answers `clipboard`; the fire-and-forget capabilities (`clipboard.set`, `open`) asked for,
with their arguments, in `caps`. -/
structure Shell where
  posted : IO.Ref (Array Host)
  clipboard : IO.Ref String
  caps : IO.Ref (Array (String × Lean.Json))

def Shell.new : IO Shell := do return { posted := ← IO.mkRef #[], clipboard := ← IO.mkRef "", caps := ← IO.mkRef #[] }

def Shell.fx (s : Shell) : LeanNative.Native.Effects Host where
  post h := s.posted.modify (·.push h)
  cap name args _ := s.caps.modify (·.push (name, args))
  ask name _ := do
    if name == "clipboard.get" then return Task.pure (Lean.Json.mkObj [("text", Lean.Json.str (← s.clipboard.get))])
    return Task.pure (Lean.Json.mkObj [("ok", Lean.Json.bool true)])

/-- How many answers `perform` posts for the commands these flows run; none for the ones they leave out
(networking, the mempool window, timers, the clipboard's copy, the journal). -/
def answersTo : Cmd → Option Nat
  | .refresh .. => some 3
  | .saveSettings .. | .removeExport .. => some 0
  | .receiveAddress .. | .setReceiveLabel .. | .ownCard .. | .parsePaste .. | .addPerson .. | .editPerson ..
  | .updateRecipient .. | .labelSender .. | .removeSenderLabel .. | .catalogStatus .. | .connectedPeers ..
  | .resetPeers .. | .reconnect .. | .loadPaymentDetails .. | .exportBundle .. | .revealPhrase ..
  | .deleteWallet .. | .paste .. | .importWallet .. => some 1
  | _ => none

/-- Runs `cs` through `perform`, each answer back through `onHost` and whatever that asks for in turn; the
model after, and the commands left out, in order. -/
partial def Shell.run (s : Shell) (m : Model) (cs : List Cmd) : IO (Model × List Cmd) := do
  let mut m := m
  let mut left : List Cmd := []
  for c in cs do
    match answersTo c with
    | none => left := left ++ [c]
    | some n =>
      let before := (← s.posted.get).size
      WinnowApp.perform c s.fx
      unless ← waitUntil 10_000 (every := 2) (do return (← s.posted.get).size ≥ before + n) do
        throw (IO.userError "a command posted no answer within 10 s")
      for h in (← s.posted.get).extract before (before + n) do
        let (m', cs') := onHost h m
        let (m', rest) ← s.run m' cs'
        m := m'
        left := left ++ rest
  return (m, left)

/-- A tap: `step`, then its commands as `run` runs them. -/
def Shell.tap (s : Shell) (msg : Msg) (m : Model) : IO (Model × List Cmd) := do
  let (m, cs) := step msg m
  s.run m cs

/-- The whole tree as the shell receives it. -/
def rendered (m : Model) : String := (LeanNative.Html.toWire (view m)).toJson.compress
def renderedH (h : H) : String := (LeanNative.Html.toWire h).toJson.compress

/-- A ready regtest phone on the real backend: `Wallet.create` in its own directory, opened by
`Backend.realWithMultisig` with no network (no peer, no HTTPS). -/
def screenPhone (root : System.FilePath) (name : String) (entropy : UInt8) : IO (Backend × String) := do
  let dir := root / name / "regtest"
  IO.FS.createDirAll dir
  let ks := inMemoryKeyStore (← IO.mkRef {})
  match ← (Wallet.create network ks (some (dir / "wallet.json")) (entropy := some (ByteArray.mk (Array.replicate 16 entropy)))).run with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"Wallet.create: {e.name}")
  let (backend, _, _) ← Backend.realWithMultisig { keyStore := ks, fetch := fun _ => throw (.other "offline") }
  match ← backend.openWallet .regtest dir.toString with
  | .opened id => return (backend, id)
  | _ => throw (IO.userError s!"{name}: the wallet did not open")

/-- The model of a ready phone on regtest, in the foreground. -/
def readyModel (walletID : String) (advanced := false) : Model :=
  { stage := .ready, active := true, walletID := some walletID,
    settings := { network := .regtest, advancedMode := advanced } }

/-! ### Model.fail (#48) -/

/-- Every busy flag a failure can clear, by name, as one model has them all set. -/
def busyFlags : List (String × (Model → Bool)) :=
  [ ("onboarding.busy", (·.onboarding.busy)), ("onboarding.restoring", (·.onboarding.restoring))
  , ("receive.changing", (·.receive.changing)), ("labelEditor.saving", (·.labelEditor.saving))
  , ("send.reviewing", (·.send.reviewing)), ("send.sending", (·.send.sending))
  , ("spendingInFlight", (·.spendingInFlight)), ("settingsDraft.resettingPeers", (·.settingsDraft.resettingPeers))
  , ("payment.loading", (·.payment.loading)), ("feeBump.bumping", (·.feeBump.bumping))
  , ("exportState.busy", (·.exportState.busy)), ("reveal.revealing", (·.reveal.revealing))
  , ("person.saving", (·.person.saving)), ("person.inferring", (·.person.inferring))
  , ("multisigAdd.saving", (·.multisigAdd.saving)), ("multisigBuild.creating", (·.multisigBuild.creating))
  , ("ledgerPair.pairing", (·.ledgerPair.pairing)), ("signerKeys.saving", (·.signerKeys.saving))
  , ("collect.busy", (·.collect.busy)) ]

/-- A phone with every screen in the middle of something: each busy flag set, the export holding a file, a
card shown, the collection step at epoch 4. -/
def busyModel : Model :=
  { readyModel "w" with
    onboarding := { busy := true, restoring := true }
    receive := { address := "bcrt1q", changing := true }
    labelEditor := { address := "bcrt1q", draft := "Rent", saving := true }
    send := { reviewing := true, sending := true, resolvedRateMilli := some 2_000 }
    spendingInFlight := true
    settingsDraft := { resettingPeers := true }
    payment := { loading := true }
    feeBump := { txid := "tt", bumping := true }
    exportState := { busy := true, file := some "/tmp/winnow-export-x/w.json" }
    reveal := { revealing := true }
    person := { saving := true, inferring := true }
    shareCard := { card := some "card" }
    multisigAdd := { saving := true }
    multisigBuild := { creating := true }
    ledgerPair := { pairing := true }
    signerKeys := { saving := true }
    collect := { busy := true, epoch := 4 } }

/-- `Model.fail` for each context it handles: where the message lands, and the busy flags it clears; every
other flag stays set (a failure touches only the screen that asked). -/
def failTable : List (String × (Model → Bool) × List String) :=
  let boom := some "boom"
  [ ("create", (·.onboarding.error == boom), ["onboarding.busy"])
  , ("import", (·.onboarding.error == boom), ["onboarding.busy"])
  , ("onboarding", (·.onboarding.error == boom), ["onboarding.busy"])
  , ("create.cancelled", (·.onboarding.error.isNone), ["onboarding.busy"])
  , ("import.cancelled", (·.onboarding.error.isNone), ["onboarding.busy"])
  , ("cloudRestore", (·.onboarding.restoreError == boom), ["onboarding.restoring"])
  , ("cloudRestore.cancelled", (·.onboarding.restoreError.isNone), ["onboarding.restoring"])
  , ("reveal.cancelled", (·.reveal.error.isNone), ["reveal.revealing"])
  , ("receive", (·.receive.error == boom), ["receive.changing"])
  , ("label", (·.labelEditor.error == boom), ["labelEditor.saving"])
  , ("send", (·.send.error == boom), ["send.reviewing", "send.sending", "spendingInFlight"])
  -- a declined Face ID before a payment: the prompt's text shows, and Send is free again
  , ("send.cancelled", (·.send.error == boom), ["send.reviewing", "send.sending", "spendingInFlight"])
  , ("rate", (·.send.resolvedRateMilli.isNone), [])
  , ("settings", (·.settingsDraft.error == boom), ["settingsDraft.resettingPeers"])
  , ("peers", (·.settingsDraft.error == boom), ["settingsDraft.resettingPeers"])
  , ("delete", (·.confirm == some (.deleteFailed "boom")), [])
  , ("catalog", (·.settingsDraft.catalog.isNone), [])
  , ("payment", (·.payment.error == boom), ["payment.loading"])
  , ("feeBump", (·.feeBump.error == boom), ["feeBump.bumping", "spendingInFlight"])
  , ("feeBump.cancelled", (·.feeBump.error == boom), ["feeBump.bumping", "spendingInFlight"])
  , ("export", fun m => m.exportState.error == boom && m.exportState.file.isNone, ["exportState.busy"])
  , ("reveal", (·.reveal.error == boom), ["reveal.revealing"])
  , ("card", fun m => m.shareCard.error == boom && m.shareCard.card.isNone, [])
  , ("person", (·.person.error == boom), ["person.saving", "person.inferring"])
  , ("recipients", (·.recipientsError == boom), [])
  , ("multisigAdd", (·.multisigAdd.error == boom), ["multisigAdd.saving"])
  , ("multisigBuild", (·.multisigBuild.error == boom), ["multisigBuild.creating"])
  , ("multisigAccount", (·.multisigAccountError == boom), [])
  , ("accountSpend", (·.payment.error == boom), [])
  , ("ledgerPair", (·.ledgerPair.error == boom), ["ledgerPair.pairing"])
  , ("signerKeys", (·.signerKeys.error == boom), ["signerKeys.saving"])
  , ("signer", (·.signerDetail.error == boom), [])
  , ("multisigOverview", (·.status.lastSyncError.isNone), [])
  , ("collect.4", (·.collect.error == boom), ["collect.busy", "spendingInFlight"])
  , ("collect.4.cancelled", (·.collect.error.isNone), ["collect.busy", "spendingInFlight"])
  -- an earlier collection run's failure: dropped, though the spend it held is free again
  , ("collect.3", (·.collect.error.isNone), ["spendingInFlight"])
  -- what no screen asked for falls through to the sync error line
  , ("refresh", (·.status.lastSyncError == boom), [])
  , ("sync", (·.status.lastSyncError == boom), [])
  , ("open", (·.status.lastSyncError == boom), [])
  , ("somethingNew", (·.status.lastSyncError == boom), []) ]

/-- #48: each failure reaches the screen that asked and clears that screen's busy flags, through `onHost`
as `perform` posts it; the screens then show it. -/
def failuresReachTheirScreens : IO Unit := do
  for (name, flag) in busyFlags do
    check s!"fail: the busy model has {name} set" (flag busyModel)
  for (ctx, landed, clears) in failTable do
    let (m, cs) := onHost (.failed busyModel.generation ctx "boom") busyModel
    check s!"fail {ctx}: the message lands on its screen" (landed m && cs.isEmpty)
    for (name, flag) in busyFlags do
      if clears.contains name then check s!"fail {ctx}: clears {name}" (!flag m)
      else check s!"fail {ctx}: leaves {name}" (flag m)
  -- a cancelled restore leaves an earlier message alone; a cancelled iCloud prompt says nothing
  let restoring := { busyModel with onboarding := { busyModel.onboarding with restoreError := some "earlier" } }
  check "fail cloudRestore.cancelled: keeps what the restore said" ((restoring.fail "cloudRestore.cancelled" "x").onboarding.restoreError == some "earlier")
  check "fail cloudRestore: a CancellationError says nothing" ((busyModel.fail "cloudRestore" "Winnow.CancellationError").onboarding.restoreError.isNone)
  -- the collection step only while the scene is active
  let away := (busyModel.fail "collect.4" "boom")
  check "fail collect: the active scene's run shows" (away.collect.error == some "boom")
  let background := { busyModel with active := false }.fail "collect.4" "boom"
  check "fail collect: not while in the background" (background.collect.busy && background.collect.error.isNone && !background.spendingInFlight)
  check "fail collect: a context that is not a number is an earlier run's" ((busyModel.fail "collect.x" "boom").collect.busy)
  -- another wallet's failure is dropped (a network switch since)
  let (switched, _) := busyModel.switchNetwork .mainnet
  let (other, _) := onHost (.failed busyModel.generation "send" "boom") { switched with send := { sending := true } }
  check "fail: another wallet's failure is dropped" (other.send.sending && other.send.error.isNone)
  -- the screens show it: Send's review, the fee bump, Pair a Ledger, the label editor
  let sending := { readyModel "w" with send := { sending := true, preview := none }, spendingInFlight := true }.present .send
  let (m, _) := onHost (.failed 0 "send" Real.AppError.sendReviewChanged.text) sending
  check "fail send: Send shows why, and can be used again" (contains (rendered m) Real.AppError.sendReviewChanged.text && !m.send.sending)
  let replacedRow : HistoryItem := { txid := "tt", height := 0, received := 0, spent := 1000, fee := some 100, replacedBy := some "rr" }
  let sent := { (readyModel "w") with send := { sentTxid := some "tt" } }.present .send
  check "a sent payment waits for its confirmation" (contains (rendered sent) "Waiting for confirmation")
  let gone := { sent with status := { sent.status with history := [replacedRow] } }
  check "Send stops waiting once the payment is replaced" (contains (rendered gone) "Replaced" && !contains (rendered gone) "Waiting for confirmation")
  let opened := { sent with expanded := ["send.details"] }
  check "a new payment starts with its details closed" (!(stepSend .newPayment opened).1.isExpanded "send.details")
  check "so does Send opened again" (!(opened.closeSheet .send).1.isExpanded "send.details")
  let review : WinnowApp.FeeBumpPreview := { feeRateMilli := 5_000, fee := 700, change := some 9_300 }
  let bump : FeeBump := { txid := "tt", bumping := true, targetText := "5", reviewed := some ("5", review) }
  let bumping := { readyModel "w" (advanced := true) with feeBump := bump }.present .feeBump
  check "fail feeBump: the sheet says Signing while it runs" (contains (rendered bumping) "Signing & broadcasting")
  let (m, _) := onHost (.failed 0 "feeBump" "The replacement was refused") bumping
  check "fail feeBump: the sheet shows it and offers Sign & replace again"
    (contains (rendered m) "The replacement was refused" && contains (rendered m) "Sign & replace" && !m.spendingInFlight)
  let pairing := { readyModel "w" (advanced := true) with routes := [.ledgerPair], ledgerPair := { name := "Nano X", pairing := true } }
  let (m, _) := onHost (.failed 0 "ledgerPair" "No Ledger answered") pairing
  check "fail ledgerPair: Pair a Ledger shows it, Pair again" (contains (rendered m) "No Ledger answered" && contains (rendered m) "\"Pair\"")
  let unknown := (onHost (.failed 0 "somethingNew" "the sync line") (readyModel "w" (advanced := true))).1
  check "fail: an unknown context shows on the Sync line" (contains (rendered unknown) "the sync line")

/-! ### Settings (#44) -/

/-- A backend that answers the Settings screen and records what reached it. -/
def recordingBackend (calls : IO.Ref (Array String)) (failReset : IO.Ref Bool) : Backend :=
  let note (s : String) : IO Unit := calls.modify (·.push s)
  { Backend.pending with
    reconnect := fun s => note s!"reconnect {s.scoped.manualPeers} genesis={s.verifyFromGenesis}"
    snapshot := do note "snapshot"; return ({}, .synced)
    records := do note "records"; return {}
    multisigOverview := do note "multisigOverview"; return {}
    catalogStatus := do note "catalogStatus"; return "Observed 2026-09-28: 412 candidates."
    connectedPeers := do
      note "connectedPeers"
      return [{ endpoint := "203.0.113.7:8333", userAgent := "/Satoshi:30.0/", startHeight := 900_000, feeFilter := some 1_000 }]
    resetPeers := do
      note "resetPeers"
      if ← failReset.get then throw (IO.userError "The peer store could not be cleared.")
    updateSettings := fun s => note s!"updateSettings {s.scoped.manualPeers} {reprStr s.scoped.explorer} {s.scoped.esploraURL} genesis={s.verifyFromGenesis}"
    exportBundle := fun withPhrase => do note s!"exportBundle {withPhrase}"; return "{\"version\":1}"
    revealMnemonic := do note "revealMnemonic"; return ["abandon", "ability", "able"]
    deleteWallet := note "deleteWallet" }

/-- #44: Settings' controls, each through `perform` to the backend, each change saved (the command, the
settings file and the backend's copy) and shown. -/
def settingsScreen (root : System.FilePath) : IO Unit := do
  let calls ← IO.mkRef (#[] : Array String)
  let failReset ← IO.mkRef false
  backendRef.set (recordingBackend calls failReset)
  rootDir.set (root / "settings").toString
  IO.FS.createDirAll (root / "settings")
  tmpDir.set (root / "tmp").toString
  IO.FS.createDirAll (root / "tmp")
  let sh ← Shell.new
  let called (s : String) : IO Bool := do return (← calls.get).contains s
  let savedFile : IO Settings := do
    match Lean.Json.parse (← IO.FS.readFile (root / "settings" / "settings.json")) >>= Lean.fromJson? with
    | .ok s => return s
    | .error _ => return {}
  let saved (f : Settings → Bool) : IO Bool := waitUntil 5_000 (every := 5) do
    try return f (← savedFile) catch _ => return false
  let tap (msg : SettingsMsg) (m : Model) := sh.tap (.settings msg) m
  -- the Settings tab: the census line and the connected peers load as it appears
  let m := readyModel "w" (advanced := true)
  let (m, _) ← sh.tap (.selectTab 2) m
  check "settings: the tab asks for the peers and the census line" ((← called "connectedPeers") && (← called "catalogStatus"))
  check "settings: both shown" (contains (rendered m) "Observed 2026-09-28: 412 candidates." && contains (rendered m) "203.0.113.7:8333" &&
    contains (rendered m) "floor 1000 sat/kvB")
  -- a manual peer: added, saved and shown; the same one again changes nothing; nonsense is refused
  let (m, _) ← tap (.setManualPeer " 127.0.0.1:18444 ") m
  let (m, left) ← tap .addManualPeer m
  check "manual peer: added to this network's settings" (m.settings.manualPeers == ["127.0.0.1:18444"] && m.settingsDraft.manualPeer.isEmpty && left.isEmpty)
  check "manual peer: saved to settings.json" (← saved (·.regtest.manualPeers == ["127.0.0.1:18444"]))
  check "manual peer: the backend has it" (← waitUntil 2_000 (every := 5) (called "updateSettings [127.0.0.1:18444] WinnowApp.Explorer.blockstream  genesis=false"))
  check "manual peer: shown with Remove" (contains (rendered m) "127.0.0.1:18444" && contains (rendered m) "Remove")
  check "manual peer: only this network's" (m.settings.mainnet.manualPeers.isEmpty && m.settings.signet.manualPeers.isEmpty)
  let (again, cs) := stepSettings .addManualPeer (stepSettings (.setManualPeer "127.0.0.1:18444") m).1
  check "manual peer: the same one again is not saved twice" (cs.isEmpty && again.settings.manualPeers.length == 1)
  let (bad, cs) := stepSettings .addManualPeer (stepSettings (.setManualPeer "no port here") m).1
  check "manual peer: nonsense is refused on the screen" (cs.isEmpty && contains (rendered bad) "use host:port.")
  let (m, _) ← tap (.setManualPeer "peer.example:8333") m
  let (m, _) ← tap .addManualPeer m
  check "manual peer: a second one" (m.settings.manualPeers == ["127.0.0.1:18444", "peer.example:8333"])
  let (m, _) ← tap (.removeManualPeer 0) m
  check "manual peer: removed" (m.settings.manualPeers == ["peer.example:8333"] && !contains (rendered m) "127.0.0.1:18444")
  check "manual peer: the removal is saved" (← saved (·.regtest.manualPeers == ["peer.example:8333"])) (← IO.FS.readFile (root / "settings" / "settings.json"))
  -- Reconnect: the backend rebuilds networking with the settings as saved
  let (m, _) ← tap .reconnect m
  check "Reconnect peers: reaches the backend with the saved peers" (← called "reconnect [peer.example:8333] genesis=false")
  -- Verify from genesis: saved, journaled, and networking rebuilt with it
  let (m', cs) := stepSettings (.setVerifyFromGenesis true) m
  check "Verify from genesis: saves, journals and reconnects"
    (cs.any (· matches .saveSettings _) && cs.any (· matches .journal "setting.verifyFromGenesis" _) && cs.any (· matches .reconnect ..))
  let (m, _) ← sh.run m' cs
  check "Verify from genesis: the backend reconnects from block 0" (← called "reconnect [peer.example:8333] genesis=true")
  check "Verify from genesis: saved" (← saved (·.verifyFromGenesis))
  check "Verify from genesis: the toggle is on, with its note" (contains (rendered m) "Turning this off later keeps the chain you already verified.")
  check "Verify from genesis: the same value again does nothing" (stepSettings (.setVerifyFromGenesis true) m).2.isEmpty
  -- the explorer: a preset, then a custom Esplora URL
  let (m, _) ← tap (.setExplorer 1) m
  check "explorer: mempool.space saved" (m.settings.scoped.explorer == .mempool)
  check "explorer: no URL field for a preset" (!contains (rendered m) "Esplora-compatible website URL")
  let (m, _) ← tap (.setExplorer 2) m
  check "explorer: Custom shows the URL field" (contains (rendered m) "Esplora-compatible website URL")
  let (m, _) ← tap (.setEsploraURL "  https://esplora.example/api  ") m
  check "explorer: the custom URL is saved trimmed" (m.settings.scoped.esploraURL == "https://esplora.example/api" && m.settings.scoped.explorer == .custom)
  check "explorer: saved to settings.json" (← saved fun s => s.regtest.explorer == .custom && s.regtest.esploraURL == "https://esplora.example/api")
  check "explorer: the backend has it"
    (← waitUntil 2_000 (every := 5) (called "updateSettings [peer.example:8333] WinnowApp.Explorer.custom https://esplora.example/api genesis=true"))
  check "explorer: Selected shows it" (contains (rendered m) "Selected: https://esplora.example/api")
  check "explorer: a relaunch keeps it" ((relaunch m.settings).esploraBaseURL == "https://esplora.example/api")
  check "explorer: an index past the list does nothing" (stepSettings (.setExplorer 7) m).2.isEmpty
  -- what the explorer trades away, and the design papers
  let (side, _) := stepSettings .openReadSide m
  check "read side: the sheet" (side.topSheet == some .readSide && contains (renderedH (readSideSheet [])) "read-side.html" &&
    contains (rendered side) "The Read Side")
  let (closed, _) := step .closeSheet side
  check "read side: closes" closed.sheets.isEmpty
  let (papers, _) := stepSettings .openPapers m
  let list := renderedH (papersSheet papers [])
  check "papers: the four" (contains list "A phone wallet" && contains list "The read side" && contains list "The write side" && contains list "Import")
  let (paper, _) := stepSettings (.openPaper 2) papers
  check "papers: one opens as its page" (contains (renderedH (papersSheet paper [])) "write-side.html" && contains (rendered paper) "write-side.html")
  let (back, _) := stepSettings .closePaper paper
  check "papers: back to the list" (back.paper.isNone && contains (renderedH (papersSheet back [])) "A phone wallet")
  let (done, _) := step .closeSheet paper
  check "papers: closing forgets the page" (done.sheets.isEmpty && done.paper.isNone)
  -- Refresh and Reset peers
  calls.set #[]
  let (m, _) ← tap .refreshPeers m
  check "Refresh: asks the backend for the peers" (← called "connectedPeers")
  let (asking, _) ← tap .askResetPeers m
  check "Reset peers: asks first" (asking.confirm == some .resetPeers && contains (rendered asking) "Reset and shuffle peers?")
  let (resetting, cs) := stepSettings .resetPeers asking
  check "Reset peers: Resetting… while it runs" (resetting.settingsDraft.resettingPeers && contains (rendered resetting) "Resetting" &&
    resetting.confirm.isNone && cs.any (· matches .resetPeers _))
  let (m, _) ← sh.run resetting cs
  check "Reset peers: the backend resets, then the peers and the wallet are read again"
    ((← called "resetPeers") && (← called "connectedPeers") && (← called "snapshot") && !m.settingsDraft.resettingPeers)
  check "Reset peers: the button is back" (contains (rendered m) "Reset and shuffle peers" && !contains (rendered m) "Resetting")
  failReset.set true
  let (failed, _) ← sh.run (stepSettings .resetPeers m).1 (stepSettings .resetPeers m).2
  check "Reset peers: a failure shows and frees the button"
    (!failed.settingsDraft.resettingPeers && contains (rendered failed) "The peer store could not be cleared.")
  -- Check gateways and reconnect: not while a discovery runs
  check "Check gateways: reconnects" ((stepSettings .checkGateways m).2.any (· matches .reconnect ..))
  check "Check gateways: not while discovering" (stepSettings .checkGateways { m with status := { discoveringGateways := true } }).2.isEmpty
  -- the backup file and the recovery phrase reach the backend too (performSettings' other commands)
  let (exp, _) := stepBackup .openExport m
  let (exp, cs) := stepBackup .createExport exp
  let (exp, _) ← sh.run exp cs
  check "export: the backend's bundle, staged as a file" ((← called "exportBundle false") && exp.exportState.file.isSome && !exp.exportState.busy)
  let file := exp.exportState.file.getD ""
  check "export: the file holds the bundle" ((← IO.FS.readFile file) == "{\"version\":1}")
  let (gone, cs) := step .closeSheet exp
  let (_, _) ← sh.run gone cs
  check "export: closing the sheet removes the staged file" (← waitUntil 2_000 (every := 5) do return !(← System.FilePath.pathExists file))
  let (rev, _) ← sh.tap (.backup .reveal) m
  check "reveal: the words, after device authentication" ((← called "revealMnemonic") && rev.reveal.words == ["abandon", "ability", "able"] &&
    rev.topSheet == some .revealPhrase)
  -- Delete wallet: asks, then the backend deletes and onboarding comes back
  let (asking, _) ← tap .askDelete m
  check "delete: asks first" (asking.confirm == some .deleteWallet && contains (rendered asking) "Delete this wallet?")
  let (deleted, _) ← tap .deleteWallet asking
  check "delete: the backend deletes, onboarding" ((← called "deleteWallet") && deleted.stage == .onboarding && deleted.walletID.isNone)
  backendRef.set Backend.pending

/-! ### Receive (#45) -/

/-- #45: Receive's controls on the real backend: New address, a label saved, renamed and removed, and the
share card with a display name. -/
def receiveScreen (sh : Shell) (backend : Backend) (walletID : String) : IO Unit := do
  let m := readyModel walletID
  let (m, left) ← sh.tap .openReceive m
  let first := m.receive.address
  check "receive: the first address" (first.startsWith "bcrt1p" && m.topSheet == some .receive) first
  check "receive: the mempool window opens on it" (left.any fun | .watchAddress _ a => a == first | _ => false)
  check "receive: an unlabelled address asks who it is for first"
    (m.receive.editingLabel && contains (rendered m) "Who is this address for?" && contains (rendered m) "Skip for now")
  let (m, _) ← sh.tap (.receive .finishLabel) m
  check "receive: Skip shows the address" (!m.receive.editingLabel && contains (rendered m) first && contains (rendered m) "Label this address")
  -- New address
  let (m, left) ← sh.tap (.receive .freshAddress) m
  let second := m.receive.address
  check "New address: differs from the first" (second.startsWith "bcrt1p" && second != first) second
  check "New address: the mempool window moves to it"
    (left.any (· matches .stopWatchingAddress) && left.any fun | .watchAddress _ a => a == second | _ => false)
  check "New address: the label editor comes first" (m.receive.editingLabel && !m.receive.changing && m.labelEditor.address == second)
  -- label it
  let (m, _) ← sh.tap (.receive (.setLabelDraft "  Alice, invoice 12 ")) m
  let (m, _) ← sh.tap (.receive .saveLabel) m
  check "label: saved for the new address only, trimmed"
    (lookup m.records.receiveLabels second == some "Alice, invoice 12" && (lookup m.records.receiveLabels first).isNone)
  check "label: back to the address, the label above it"
    (!m.receive.editingLabel && contains (rendered m) "Alice, invoice 12" && contains (rendered m) "Edit label")
  -- rename it
  let (m, _) ← sh.tap (.receive .editLabel) m
  check "rename: the editor holds the label" (m.labelEditor.draft == "Alice, invoice 12" && contains (rendered m) "Save label" &&
    contains (rendered m) "Remove label")
  let (twoLines, _) := stepReceive (.setLabelDraft "Alice\ninvoice") m
  check "rename: two lines are refused on the screen"
    ((stepReceive .saveLabel twoLines).2.isEmpty && contains (rendered twoLines) "Use a single-line label of at most 120 characters.")
  let (m, _) ← sh.tap (.receive (.setLabelDraft "Alice, invoice 13")) m
  let (m, _) ← sh.tap (.receive .saveLabel) m
  check "rename: the new label" (lookup m.records.receiveLabels second == some "Alice, invoice 13" &&
    contains (rendered m) "Alice, invoice 13" && !contains (rendered m) "invoice 12")
  -- remove it
  let (m, _) ← sh.tap (.receive .editLabel) m
  let (m, _) ← sh.tap (.receive .removeLabel) m
  check "remove: the label is gone" ((lookup m.records.receiveLabels second).isNone && !m.receive.editingLabel &&
    contains (rendered m) "Label this address")
  check "remove: and the backend agrees" ((lookup (← backend.records).receiveLabels second).isNone)
  -- the share card: no name yet, then one
  let (card, cs) := stepReceive .openCard m
  check "card: the sheet opens, and asks for a name" (card.topSheet == some .shareCard && !cs.any (· matches .ownCard ..) &&
    contains (renderedH (shareCardSheet card [])) "Add a name to make your card.")
  let (card, left) ← sh.tap (.receive (.setOwnName "Alice")) card
  check "card: the name is saved" (card.settings.ownDisplayName == "Alice" && left.isEmpty)
  let shown := renderedH (shareCardSheet card [])
  let some text := card.shareCard.card | check "card: made for the name" false; return
  check "card: shown with its QR code" (contains shown "Your card" && contains shown "\"qr\"")
  let read ← backend.parsePaste text
  check "card: another phone reads Alice and a fresh address each payment" (read.name == some "Alice" && read.payTo == some true)
  let (named, cs) := stepReceive .openCard { m with settings := { m.settings with ownDisplayName := "Alice" } }
  check "card: opening it with a name set asks for the card" (cs.any fun | .ownCard _ n => n == "Alice" | _ => false)
  let (named, _) ← sh.run named cs
  check "card: the card arrives" (named.shareCard.card == some text)
  let stale := onHost (.card named.generation "Bob" "other") named
  check "card: one made for another name is dropped" (stale.1.shareCard.card == some text)
  let (cleared, _) ← sh.tap (.receive (.setOwnName "  ")) card
  check "card: an empty name takes the card away" (cleared.shareCard.card.isNone &&
    contains (renderedH (shareCardSheet cleared [])) "Add a name to make your card.")
  let (closed, cs) := step .closeSheet m
  check "receive: Done closes the sheet and the mempool window" (closed.sheets.isEmpty && cs.any (· matches .stopWatchingAddress))

/-! ### People (#35) -/

/-- #35: Saved recipients from Send: a person added from a card, renamed, a refused paste and a refused
duplicate, a person added from an address and removed, and one chosen to pay. Returns the model, Robert's id. -/
def peopleScreens (sh : Shell) (backend : Backend) (walletID cardB addressB : String) : IO (Model × String) := do
  let m := readyModel walletID
  let (m, _) ← sh.tap .openSend m
  let (m, _) ← sh.tap (.send .openRecipients) m
  check "people: Saved recipients, empty" (m.topSheet == some .savedRecipients &&
    contains (rendered m) "Save a recipient from a payment in Wallet, or add an address or card here.")
  -- add Bob from his card
  let (m, _) ← sh.tap (.people (.openAdd {} "")) m
  check "add: the sheet" (m.topSheet == some .addPerson && contains (renderedH (addPersonSheet m [])) "Save recipient")
  let (m, _) ← sh.tap (.people (.setName "Bob")) m
  let (m, _) ← sh.tap (.people (.setPasted cardB)) m
  check "add: the card reads as fresh addresses" (m.person.parsed == some { name := some "Bob", payTo := some true } &&
    contains (renderedH (addPersonSheet m [])) "Fresh address each payment")
  check "add: Save is enabled" (m.person.canSave m)
  let (m, _) ← sh.tap (.people .save) m
  let some bob := m.records.people.find? (·.name == "Bob") | check "add: Bob saved" false; return (m, "")
  check "add: the sheet closes on the list" (m.topSheet == some .savedRecipients && bob.payTo == some true)
  check "add: the list shows Bob with Rename and Remove" (contains (rendered m) "\"Bob\"" && contains (rendered m) "Rename")
  -- rename him
  let (m, _) ← sh.tap (.people (.rename bob.id)) m
  let sheet := renderedH (addPersonSheet m [])
  check "rename: the sheet, his name in it, no paste field" (contains sheet "Rename recipient" && m.person.name == "Bob" &&
    !contains sheet "Paste an address or card")
  let (m, _) ← sh.tap (.people (.setName "Robert")) m
  let (m, _) ← sh.tap (.people .save) m
  check "rename: saved" ((m.person? bob.id).map (·.name) == some "Robert" && m.topSheet == some .savedRecipients &&
    contains (rendered m) "Robert")
  -- what is refused: a paste that is no address or card, the same card under another name
  let (m, _) ← sh.tap (.people (.openAdd {} "")) m
  let (m, _) ← sh.tap (.people (.setName "Bobby")) m
  let (garbage, _) ← sh.tap (.people (.setPasted "hello world")) m
  check "refused: a paste that is not an address or card says so, and Save is off"
    (garbage.person.error.isSome && !garbage.person.canSave garbage && (stepPeople .save garbage).2.isEmpty &&
     contains (renderedH (addPersonSheet garbage [])) (garbage.person.error.getD "?"))
  let (dup, _) ← sh.tap (.people (.setPasted cardB)) garbage
  let (dup, _) ← sh.tap (.people .save) dup
  check "refused: the same card twice, on the sheet" (dup.topSheet == some .addPerson && !dup.person.saving &&
    dup.person.error.isSome && contains (renderedH (addPersonSheet dup [])) "Robert")
  let (m, _) ← sh.tap .closeSheet dup
  -- Carol, by one address, then removed
  let (m, _) ← sh.tap (.people (.openAdd {} addressB)) m
  check "add: an address pasted in the sheet" (m.person.parsed.bind (·.payTo) == some false &&
    contains (renderedH (addPersonSheet m [])) "Uses this same address each time")
  let (m, _) ← sh.tap (.people (.setName "Carol")) m
  let (m, _) ← sh.tap (.people .save) m
  let some carol := m.records.people.find? (·.name == "Carol") | check "add: Carol saved" false; return (m, bob.id)
  check "add: Carol listed" (contains (rendered m) "Carol")
  let (m, _) ← sh.tap (.people (.remove carol.id)) m
  check "remove: Carol is no longer a saved recipient" (!contains (rendered m) "Carol" &&
    ((m.person? carol.id).map (·.isSavedRecipient)) == some false && m.recipientsError.isNone)
  check "remove: the backend agrees" (((← backend.records).people.find? (·.id == carol.id)).map (·.isSavedRecipient) == some false)
  -- choose Robert to pay
  let (m, _) ← sh.tap (.people (.choose bob.id)) m
  check "choose: back on Send, paying Robert" (m.topSheet == some .send && m.send.inputs.personID == some bob.id &&
    contains (rendered m) "Robert" && contains (rendered m) "Change")
  let (m, _) := step .closeSheet m
  return (m, bob.id)

/-! ### Home: a payment's screen (#35) -/

def scriptHex (address : String) : IO String := do
  match AddressDecoder.scriptPubKey address network with
  | .ok s => return hex s
  | .error _ => throw (IO.userError s!"no script for {address}")

/-- #35: Home's payment screen over three payments, the people the flow above saved and a receive label:
each section, and what its buttons do, through the real backend. -/
def homeScreens (sh : Shell) (backend : Backend) (walletID robertID bobAddress ownAddress funder : String) : IO Unit := do
  discard <| backend.setReceiveLabel ownAddress "Invoice 12"
  let records ← backend.records
  let bobScript ← scriptHex bobAddress
  check "home fixture: Robert's first address is one of his" (records.recipientByScript.contains (bobScript, robertID))
  let t1 := hex (ByteArray.mk (Array.replicate 32 0x11))
  let t2 := hex (ByteArray.mk (Array.replicate 32 0x22))
  let t3 := hex (ByteArray.mk (Array.replicate 32 0x33))
  let ownScript ← scriptHex ownAddress
  let toBob : TxOut := { index := 0, address := some bobAddress, script := bobScript, amount := 50_000, ownedByWallet := false }
  let change : TxOut := { index := 1, address := some "bcrt1qchange", script := "0014", amount := 9_500, ownedByWallet := true }
  let toUs : TxOut := { index := 0, address := some ownAddress, script := ownScript, amount := 20_000, ownedByWallet := true }
  let sent : HistoryItem :=
    { txid := t1, height := 0, received := 9_500, spent := 60_000, fee := some 500, outputs := some [toBob, change] }
  let received : HistoryItem :=
    { txid := t2, height := 101, received := 20_000, spent := 0, fee := none, outputs := some [toUs], fundingAddresses := [funder] }
  let unstored : HistoryItem := { txid := t3, height := 99, received := 0, spent := 7_300, fee := some 300 }
  let history := [sent, received, unstored]
  let status : Status := { balance := 29_500, history, payments := history.map ({ item := ·, source := .wallet }),
                           feeBumpable := [t1], tipHeight := 101 }
  let m := { readyModel walletID with status, records }
  let home := rendered m
  check "home: the list" (contains home "Sent to Robert" && contains home "Received" && contains home (Ids.historyPayment t2) &&
    contains home "Pending" && contains home "Confirmed")
  -- the payment to Robert
  let (m, left) ← sh.tap (.home (.openPayment t1)) m
  check "payment: opens, nothing to load" (m.routes == [.payment t1] && left.isEmpty && !m.payment.loading)
  let sections := (paymentSections m t1).map renderedH
  check "payment: its row, its recipient, its transaction" (sections.length == 3) s!"{sections.length}"
  check "payment: the row" (contains sections[0]! "Sent to Robert" && contains sections[0]! "Pending")
  check "payment: Robert, the amount, Rename and Remove" (contains sections[1]! "Robert" && contains sections[1]! (satsText 50_000) &&
    contains sections[1]! "Rename recipient" && contains sections[1]! "Remove from saved recipients")
  check "payment: Simple mode folds the address and the transaction ID under their titles"
    (contains sections[1]! "\"Address\"" && contains sections[2]! "\"Transaction ID\"" && !contains (rendered m) "View transaction")
  let (m, _) ← sh.tap (.setExpanded s!"pay.addr.0" true) m
  let (m, _) ← sh.tap (.setExpanded "pay.txid" true) m
  check "payment: unfolded" (m.isExpanded "pay.addr.0" && m.isExpanded "pay.txid" && contains (rendered m) bobAddress && contains (rendered m) t1)
  let (opened, _) ← sh.tap (.home (.editRecipient bobAddress (some robertID))) m
  check "payment: Rename recipient opens the sheet with his name"
    (opened.topSheet == some .addPerson && opened.person.name == "Robert" && contains (rendered opened) "Rename recipient")
  let (m, _) ← sh.tap (.home (.removeRecipient robertID)) m
  check "payment: Remove from saved recipients" (((m.person? robertID).map (·.isSavedRecipient)) == some false &&
    contains (rendered m) "Save recipient" && !contains (rendered m) "Remove from saved recipients")
  let (m, _) ← sh.tap (.home (.editRecipient bobAddress (some robertID))) m
  check "payment: Save recipient, with his name" (m.person.name == "Robert" && contains (renderedH (addPersonSheet m [])) "Save recipient")
  let (m, _) ← sh.tap (.people .save) m
  check "payment: saved again" (((m.person? robertID).map (·.isSavedRecipient)) == some true && contains (rendered m) "Rename recipient" &&
    m.sheets.isEmpty)
  let (m, _) ← sh.tap (.home .pop) m
  check "payment: Back" (m.routes.isEmpty && contains (rendered m) "Activity")
  -- the payment received: its address label, its sender
  let (m, _) ← sh.tap (.home (.openPayment t2)) m
  let sections := (paymentSections m t2).map renderedH
  check "received: its row, its label, its sender, its transaction" (sections.length == 4) s!"{sections.length}"
  check "received: the label of the address paid" (contains sections[1]! "Receive address labels" && contains sections[1]! "Invoice 12" &&
    contains sections[1]! "Edit address label")
  check "received: no sender yet" (contains sections[2]! "Save sender as person")
  let (m, _) ← sh.tap (.home .labelSender) m
  let sheet := renderedH (addPersonSheet m [])
  check "sender: the sheet offers the saved people and the funding address"
    (contains sheet "Save sender" && contains sheet "Or choose someone saved" && contains sheet "Robert" && contains sheet funder)
  let (m, _) ← sh.tap (.people (.chooseFunding funder .localFunding)) m
  let (m, _) ← sh.tap (.people (.setName "Dave")) m
  let (m, _) ← sh.tap (.people .save) m
  let some dave := m.records.people.find? (·.name == "Dave") | check "sender: Dave saved" false; return
  check "sender: Dave labels the payment, paid at his funding address"
    (lookup m.records.senderByTxid t2 == some dave.id && dave.payTo == some false && dave.provenance == some .localFunding && m.sheets.isEmpty)
  let shown := rendered m
  check "sender: the screen says so" (contains shown "Received from Dave" && contains shown "Send to Dave" && contains shown "Remove sender label")
  let (paying, left) ← sh.tap (.home (.sendToPerson dave.id)) m
  check "sender: Send to Dave opens Send, paying him" (paying.topSheet == some .send && paying.send.inputs.personID == some dave.id &&
    paying.send.inputs.paymentIndex == some 0 && left.any (· matches .resolveRate ..))
  let (m, _) ← sh.tap (.home .removeSenderLabel) m
  check "sender: the label removed" ((lookup m.records.senderByTxid t2).isNone && contains (rendered m) "Save sender as person")
  let (m, _) ← sh.tap (.home .labelSender) m
  let (m, _) ← sh.tap (.people (.chooseSaved dave.id)) m
  check "sender: someone saved, chosen" (lookup m.records.senderByTxid t2 == some dave.id && m.sheets.isEmpty)
  -- the address label, edited from the payment
  let (m, _) ← sh.tap (.home (.editPaymentLabel ownAddress)) m
  let sheet := renderedH (labelSheet m [])
  check "label: the sheet, the label in it" (m.topSheet == some .labelEditor && m.labelEditor.draft == "Invoice 12" &&
    contains sheet "Address label" && contains sheet "Save label" && contains sheet "Remove label")
  let (m, _) ← sh.tap (.receive (.setLabelDraft "Invoice 12, paid")) m
  let (m, _) ← sh.tap (.receive .saveLabel) m
  check "label: saved, the sheet closes, the payment shows it" (m.sheets.isEmpty && contains (rendered m) "Invoice 12, paid")
  let (m, _) ← sh.tap (.home .pop) m
  -- a send whose transaction is not on this phone: its details load
  let (m, cs) := stepHome (.openPayment t3) m
  check "unstored: opening it loads its details" (m.payment.loading && cs.any fun | .loadPaymentDetails _ t => t == t3 | _ => false)
  check "unstored: Loading… meanwhile" (contains (rendered m) "Loading payment details")
  let (m, cs) := onHost (.paymentLoaded m.generation t3) m
  check "unstored: loaded, the wallet read again" (!m.payment.loading && cs.any (· matches .refresh _))
  let (failed, _) := onHost (.failed m.generation "payment" "The peer did not send it.") { m with payment := { loading := true } }
  check "unstored: a failure shows, with Load payment details again"
    (contains (rendered failed) "The peer did not send it." && contains (rendered failed) "Load payment details")
  check "unstored: not while syncing" (stepHome .loadPayment { failed with status := { failed.status with syncing := true } }).2.isEmpty
  let (m, _) := stepHome .pop m
  -- Advanced: the full transaction, and Bump fee for a payment that can be bumped
  let adv := { m with settings := { m.settings with advancedMode := true } }
  let (adv, _) := stepHome (.openPayment t1) adv
  let s := rendered adv
  check "Advanced: the txid in full, View transaction, Bump fee" (contains s t1 && contains s "View transaction" && contains s "Bump fee")
  let (adv2, _) := stepHome (.openPayment t2) (stepHome .pop adv).1
  check "Advanced: no Bump fee for a payment received" (!contains (rendered adv2) "Bump fee")
  -- a payment gone from the history, and the Back up page
  let (gone, _) := stepHome (.openPayment (hex (ByteArray.mk (Array.replicate 32 0x44)))) m
  check "gone: says so" (contains (rendered gone) "This payment is no longer in the wallet")
  let (backup, _) := stepHome .openBackup m
  check "Back up: the page" (backup.routes == [.backup])

/-! ### The People store: payment indexes and pay-to checks (#35) -/

/-- `advancePaymentIndex`, as two payments to Bob move it, and `validatePayTo`'s refusals, one of them
through the file. -/
def paymentIndexAndPayTo (a b : Phone) : IO Unit := do
  let r ← a.records
  let some bob := r.people.find? (·.name == "Bob") | check "Bob is saved" false; return
  let index (r : Records) : Nat := ((r.people.find? (·.id == bob.id)).map (·.nextPaymentIndex)).getD 999
  check "index: Bob is paid at index 0 first" (index r == 0)
  let (addr0, i0) ← obtain "index: Bob's next address" (nextPaymentAddress a.store bob.id)
  let advance (i : UInt32) : RM Records := withPeople a.store (some a.wallet) fun ps =>
    ps.advancePaymentIndex a.store.keys a.store.writeData bob.id i
  let r ← obtain "index: a payment at 0" (advance i0)
  check "index: the next payment uses 1" (index r == 1)
  let (addr1, i1) ← obtain "index: Bob's next address again" (nextPaymentAddress a.store bob.id)
  check "index: a fresh address" (i1 == 1 && addr1 != addr0)
  let r ← obtain "index: a payment reported at 0 again" (advance 0)
  check "index: never goes back" (index r == 1)
  let r ← obtain "index: a payment at 4" (advance 4)
  check "index: past it" (index r == 5)
  let r ← obtain "index: then one at 2" (advance 2)
  check "index: still past the highest" (index r == 5)
  check "index: on disk" (index (← (← a.reopen).records) == 5)
  refused "index: the last index there is" (kind := "invalidState") (advance PeopleStore.maximumNextIndex)
  refused "index: an unknown person" (kind := "unknownPerson") (withPeople a.store (some a.wallet) fun ps =>
    ps.advancePaymentIndex a.store.keys a.store.writeData "nobody" 1)
  -- validatePayTo
  let some bobRecord := (← a.store.read).people.record? bob.id | check "Bob's record" false; return
  let some bobPayTo := bobRecord.payTo | check "Bob's pay-to" false; return
  let person (id : String) (payTo : Winnow.PersonPayTo) : PersonRecord := { id, name := id, payTo := some payTo }
  let addr ← obtain "B address 11" (wm (b.wallet.address .receive 11))
  let seen ← obtain "payTo: Bob's descriptor" (PeopleStore.validatePayTo bobRecord network {})
  let seen ← obtain "payTo: an address" (PeopleStore.validatePayTo (person "carol" (.address addr)) network seen)
  check "payTo: both counted" (seen.size == 2)
  let seen' ← obtain "payTo: a name-only person" (PeopleStore.validatePayTo { id := "dave", name := "Dave" } network seen)
  check "payTo: a name-only person adds nothing" (seen'.size == 2)
  refused "payTo: two people with Bob's key" (kind := "invalidState") (PeopleStore.validatePayTo (person "bob2" bobPayTo) network seen)
  refused "payTo: two people with one address" (kind := "invalidState") (PeopleStore.validatePayTo (person "carol2" (.address addr)) network seen)
  refused "payTo: an address not in canonical form" (kind := "invalidState")
    (PeopleStore.validatePayTo (person "spaced" (.address s!" {addr}")) network {})
  refused "payTo: a descriptor not in canonical form" (kind := "invalidState")
    (PeopleStore.validatePayTo (person "spaced" (.descriptor s!"{bobPayTo.text}\n")) network {})
  refused "payTo: another network's address" (PeopleStore.validatePayTo (person "main" (.address "bc1qar0srrr7xfkvy5l643lydnw9re59gtzzwf5mdq")) network {})
  refused "payTo: a descriptor that is none" (PeopleStore.validatePayTo (person "junk" (.descriptor "tr(nonsense)")) network {})
  refused "payTo: a silent payment code that is none" (PeopleStore.validatePayTo (person "sp" (.silentPayment "sp1qqnotacode")) network {})
  -- a sealed file holding two people with one key reads as damage
  let path := a.dir / "people.json"
  let good ← IO.FS.readBinFile path
  let key := ((← (a.keys.key "people.regtest").run).toOption.join).getD .empty
  IO.FS.writeBinFile path (SealedStoreFile.sealed (PeopleStore.encode #[bobRecord, { bobRecord with id := "copy", name := "Copy" }] #[]) "people" network key)
  check "payTo: a file with two people sharing a key is damaged" ((← (← a.reopen).records).peopleStorageNotice == some PeopleStore.damagedStorageMessage)
  IO.FS.writeBinFile path good
  check "payTo: the good file reads again" ((← (← a.reopen).records).peopleStorageNotice.isNone)

/-! ### Refused cards, in their own words (#69) -/

/-- The Add-person sheet refuses a card for another network, one from a newer Winnow and one that is no
person card, each with the card's own text (`PersonCardError.description`), and Save stays off. -/
def cardsRefusedOnTheAddPersonSheet (sh : Shell) (walletID : String) : IO Unit := do
  let (m, _) ← sh.tap .openSend (readyModel walletID)
  let (m, _) ← sh.tap (.send .openRecipients) m
  let (m, _) ← sh.tap (.people (.openAdd {} "")) m
  let (m, _) ← sh.tap (.people (.setName "Eve")) m
  let newer := "{\"name\":\"Eve\",\"network\":\"regtest\",\"version\":2,\"winnow\":\"person-card\"}"
  let cards : List (String × String × String) := [
    ("another network's card", (PersonCard.make .mainnet "Eve" none).serialized,
      "This card is for mainnet; this wallet is on regtest."),
    ("a newer Winnow's card", newer,
      "This card was made by a newer Winnow (card version 2). Update the app to read it."),
    ("not a person card", "{\"name\":\"Eve\",\"winnow\":\"signer-card\"}", "That isn't a Winnow card.")]
  for (what, card, text) in cards do
    let (refused, _) ← sh.tap (.people (.setPasted card)) m
    check s!"card refused: {what}, in the card's words" (refused.person.error == some text) s!"{refused.person.error}"
    check s!"card refused: {what}, on the sheet, Save off"
      (contains (renderedH (addPersonSheet refused [])) text && !refused.person.canSave refused)
  discard <| sh.tap .closeSheet m

/-! ### A store's seal, refused by case (#69) -/

/-- `StoreSeal.read` with each `SealFailure`: a sealed file on a phone with no key, an unsealed one once the key
exists, a seal whose code is not hex, and a payload changed under its seal. The case names are what
`RecordsError.name` reports (the Signers merge and the journal read them). -/
def sealFailures (root : System.FilePath) : IO Unit := do
  let store : StoreSeal := { store := "people", keys := StoreKeyVault.inMemory (← IO.mkRef {}) }
  let path := root / "seal-failures.json"
  let payload := "{\"people\":[]}".toUTF8
  discard <| obtain "seal: the first write establishes the key"
    (store.write payload network path fun d p => IO.FS.writeBinFile p d)
  let sealed ← IO.FS.readBinFile path
  discard <| obtain "seal: and reads back" (store.read sealed network)
  let fresh : StoreSeal := { store with keys := StoreKeyVault.inMemory (← IO.mkRef {}) }
  let some nl := sealed.toList.idxOf? 0x0A | throw (IO.userError "seal: no newline")
  let notHex := sealed.set! (nl - 1) 0x7A
  let changed := sealed.set! (sealed.size - 2) (sealed[sealed.size - 2]! ^^^ 0x01)
  for (what, kind, x) in [
      ("a sealed file, and no key on this phone", "keyMissing", fresh.read sealed network),
      ("an unsealed file, once the key exists", "unsealed", store.read payload network),
      ("a seal that is not hex", "malformed", store.read notHex network),
      ("a payload changed under its seal", "verificationFailed", store.read changed network)] do
    refused s!"seal refused: {what}" (kind := kind)
      (matching := (·.description == "The store file could not be verified.")) x

/-! ### Backup and the recovery phrase (#64) -/

/-- Where `needle` first starts in `s`, if anywhere. -/
def positionOf (s needle : String) : Option Nat :=
  match s.splitOn needle with
  | first :: _ :: _ => some first.length
  | _ => none

/-- The arguments the shell was last asked for `clipboard.set` with, from `perform`ing the copies in `cs`
(not the badge's timer, whose answer would come back in the middle of a later flow). -/
def clipboardAsked (sh : Shell) (cs : List Cmd) : IO (Option Lean.Json) := do
  sh.caps.set #[]
  for c in cs do if c matches .copy .. then WinnowApp.perform c sh.fx
  return ((← sh.caps.get).toList.filter (·.1 == "clipboard.set")).getLast?.map (·.2)

/-- #64: the screens between `revealMnemonic` and a person's eyes, as a person uses them. Advanced mode's
Settings: Show recovery phrase, the words numbered two to a row, hidden while the screen is recorded, copied
local-only for two minutes; going to the background closes it and the other two sensitive sheets (the backup
file, Restore from a file) and forgets what they held, and a phrase that arrives after that is dropped.
Simple mode's Back up page: Save a backup file with the phrase, and on a new phone Restore from a file pastes
it through to the verification report, and that phone shows the same words. -/
def backupScreens (sh : Shell) (root : System.FilePath) (backend : Backend) (walletID : String) (entropy : UInt8) : IO Unit := do
  tmpDir.set (root / "tmp").toString
  IO.FS.createDirAll (root / "tmp")
  let expected := match Winnow.Keys.BIP39.mnemonic (ByteArray.mk (Array.replicate 16 entropy)) with
    | .ok phrase => phrase.splitOn " "
    | .error _ => []
  let labels := expected.zipIdx.map fun (w, i) => s!"{i + 1}. {w}"
  let showsWords (s : String) : Bool := expected.any fun w => contains s s!"\"{w}\"" || contains s s!". {w}\""
  -- Advanced mode's Settings tab: Show recovery phrase
  let (m, _) ← sh.tap (.selectTab 2) (readyModel walletID (advanced := true))
  let settings := rendered m
  check "reveal: Settings offers Show recovery phrase" (contains settings "Show recovery phrase" && !showsWords settings)
  let (m, _) ← sh.tap (.backup .reveal) m
  check "reveal: the sheet opens on the phone's twelve words" (m.topSheet == some .revealPhrase && expected.length == 12 &&
    m.reveal.words == expected && !m.reveal.revealing) s!"{m.reveal.words}"
  let sheet := rendered m
  check "reveal: titled Recovery phrase" (contains sheet "Recovery phrase" && contains sheet "Copy recovery phrase")
  check "reveal: each word with its number" (labels.all fun l => contains sheet s!"\"{l}\"")
  let positions := labels.filterMap (positionOf sheet s!"\"{·}\"")
  check "reveal: numbered 1 to 12 in order" (positions.length == 12 && (positions.zip positions.tail).all fun (a, b) => a < b)
  let rec pairs : List String → List (String × String)
    | a :: b :: rest => (a, b) :: pairs rest
    | _ => []
  check "reveal: two words to a row, 1 beside 2"
    (pairs labels |>.all fun (a, b) => contains sheet (renderedH (.row [body a, .spacer, body b])))
  check "reveal: six rows" ((pairs labels).length == 6 && !contains sheet "\"13. ")
  -- the screen recorded or mirrored, as the shell says it
  let some recording := system (Lean.Json.mkObj [("captured", Lean.Json.bool true)])
    | check "capture: the shell's event reads" false; return
  let (hidden, _) := onHost recording m
  let shown := rendered hidden
  check "capture: the words are hidden while the screen is recorded"
    (hidden.captured && !showsWords shown && contains shown "Hidden while the screen is being recorded or mirrored.")
  check "capture: the sheet stays, so the words come back" (hidden.topSheet == some .revealPhrase && hidden.reveal.words == expected)
  let (back, _) := onHost (.captured false) hidden
  check "capture: recording stops, the words show again"
    ((labels.all fun l => contains (rendered back) s!"\"{l}\"") && !contains (rendered back) "Hidden while the screen")
  -- Copy recovery phrase
  let (copied, cs) := step (.backup .copyPhrase) m
  check "copy: the button says how long" (contains (rendered copied) "Copied for 2 minutes")
  let phrase := " ".intercalate expected
  let some args ← clipboardAsked sh cs | check "copy: the phrase goes to the clipboard" false; return
  check "copy: the whole phrase" ((args.getObjValAs? String "text").toOption == some phrase)
  -- what the shell was asked, without the words
  let policy := s!"localOnly {(args.getObjValAs? Bool "localOnly").toOption}, expiresIn {(args.getObjValAs? Nat "expiresIn").toOption}"
  check "copy: local only, never Universal Clipboard" ((args.getObjValAs? Bool "localOnly").toOption == some true) policy
  check "copy: expires after two minutes" ((args.getObjValAs? Nat "expiresIn").toOption == some 120) policy
  let some other ← clipboardAsked sh (step (.copy "address" "bcrt1qaddress") m).2
    | check "copy: an address goes to the clipboard" false; return
  check "copy: an address is not held to the phrase's policy"
    ((other.getObjValAs? Bool "localOnly").toOption == some false && (other.getObjValAs? Nat "expiresIn").toOption == some 300)
  -- going to the background
  let some leaving := system (Lean.Json.mkObj [("scene", Lean.Json.str "background")])
    | check "background: the shell's event reads" false; return
  let (gone, _) := onHost leaving copied
  check "background: the phrase sheet closes and forgets the words"
    (gone.sheets.isEmpty && gone.reveal.words.isEmpty && !gone.reveal.copied && !showsWords (rendered gone) &&
     !contains (rendered gone) "Recovery phrase\"")
  let (again, _) := onHost (.scene true) gone
  check "background: coming back does not bring it back" (again.sheets.isEmpty && !showsWords (rendered again))
  -- a phrase asked for, then the phone locked before it arrived
  let (asking, cs) := step (.backup .reveal) again
  let (locked, _) := onHost (.scene false) asking
  let (locked, _) := onHost (.scene true) locked
  let (late, _) ← sh.run locked cs
  check "background: a phrase that arrives afterwards is dropped" (late.sheets.isEmpty && late.reveal.words.isEmpty && !showsWords (rendered late))
  -- the backup file with the phrase in it
  let (e, _) ← sh.tap (.backup .openExport) again
  let (e, _) ← sh.tap (.backup (.setIncludeMnemonic true)) e
  let (e, _) ← sh.tap (.backup .createExport) e
  let (e, _) ← sh.tap (.backup .confirmExport) e
  let some file := e.exportState.file | check "background: the backup file is made" false; return
  check "background: the backup file is made, with the phrase" (e.topSheet == some .exportBundle &&
    contains (← IO.FS.readFile file) (expected.headD "?"))
  let (eGone, cs) := onHost (.scene false) e
  let (eGone, _) ← sh.run eGone cs
  check "background: the backup file sheet closes and forgets the file"
    (eGone.sheets.isEmpty && eGone.exportState.file.isNone && !eGone.exportState.includeMnemonic &&
     !contains (rendered eGone) "Backup ready")
  check "background: and the staged file is removed" (← waitUntil 2_000 (every := 5) do return !(← System.FilePath.pathExists file))
  -- a sheet that holds no key stays
  let (cloudOpen, _) := step (.cloud .openBackup) again
  let (cloudKept, _) := onHost (.scene false) cloudOpen
  check "background: the iCloud backup sheet stays" (cloudOpen.topSheet == some .cloudBackup && cloudKept.topSheet == some .cloudBackup)
  -- Restore from a file, before a wallet exists
  let fresh : Model := { stage := .onboarding, active := true, settings := { network := .regtest } }
  let (imp, _) := step .openImport fresh
  let (imp, _) := step (.setImportText "{\"version\":1}") imp
  check "background: Restore from a file holds the pasted text" (imp.topSheet == some .importWallet &&
    contains (rendered imp) "Import wallet")
  let (impGone, _) := onHost (.scene false) imp
  check "background: Restore from a file closes and forgets the text"
    (impGone.sheets.isEmpty && impGone.onboarding.importText.isEmpty && !contains (rendered impGone) "Import wallet")

  -- Simple mode: Home's Save a backup file, the Back up page
  let simple := readyModel walletID
  check "Back up: Home offers it while nothing is backed up" (contains (rendered simple) "Save a backup file")
  let (page, _) ← sh.tap (.home .openBackup) simple
  let shown := rendered page
  check "Back up: the page" (page.routes == [.backup] && contains shown "\"Back up\"" &&
    contains shown "A backup file is a copy of this wallet you keep yourself." && contains shown "Save a backup file")
  check "Back up: no recovery words and no iCloud control in Simple mode"
    (!contains shown "Show recovery phrase" && !contains shown "iCloud backup keeps" && !showsWords shown)
  let (page, _) ← sh.tap (.backup .openExport) page
  check "Back up: Save a backup file opens the file sheet over the page"
    (page.topSheet == some .exportBundle && contains (rendered page) "Create backup file" && contains (rendered page) "\"Back up\"")
  let (page, _) ← sh.tap (.backup (.setIncludeMnemonic true)) page
  check "Back up: including the phrase says what that means" (contains (rendered page) "This file includes your phone’s signing key.")
  let (page, _) ← sh.tap (.backup .createExport) page
  check "Back up: and asks first" (contains (rendered page) "Include the recovery phrase?" && page.exportState.file.isNone)
  let (page, _) ← sh.tap (.backup .confirmExport) page
  let some file := page.exportState.file | check "Back up: the file is ready" false; return
  check "Back up: the file is ready to share" (contains (rendered page) "Backup ready" &&
    contains (rendered page) "Includes your recovery words. Keep this file private.")
  let bundle ← IO.FS.readFile file
  let (page, cs) := step .closeSheet page
  let (page, _) ← sh.run page cs
  let (home, _) ← sh.tap (.home .pop) page
  check "Back up: closing the sheet, then Back, is Home" (page.sheets.isEmpty && home.routes.isEmpty &&
    contains (rendered home) "Save a backup file")

  -- a new phone restores it: the import sheet through to the verification report
  let restoreRoot := root / "screens-restore"
  IO.FS.createDirAll (restoreRoot / "regtest")
  -- no peer to verify against here (backend-test verifies an import against a node): the wait is cut short
  let (restorer, _, _) ← Backend.realWithMultisig { keyStore := inMemoryKeyStore (← IO.mkRef {}), fetch := fun _ => throw (.other "offline"),
                                                     importPeerWaitMs := 0 }
  match ← restorer.openWallet .regtest (restoreRoot / "regtest").toString with
  | .missing => pure ()
  | _ => check "restore: the new phone has no wallet" false; return
  backendRef.set restorer
  rootDir.set restoreRoot.toString
  check "restore: onboarding offers Restore from a file" (contains (rendered fresh) "Restore from a file")
  let (r, _) ← sh.tap .openImport fresh
  let sheet := rendered r
  check "restore: the import sheet" (r.topSheet == some .importWallet && contains sheet "Import wallet" &&
    contains sheet "Paste your backup file (JSON)" && contains sheet "Import and verify" && !contains sheet "Verification report")
  sh.clipboard.set bundle
  let (r, _) ← sh.tap .pasteImport r
  check "restore: Paste from clipboard fills it" (r.onboarding.importText == bundle)
  let (r, _) ← sh.tap .importWallet r
  let some report := r.onboarding.importReport | check "restore: the verification report" false s!"{r.onboarding.error}"; return
  let sheet := rendered r
  check "restore: the verification report, then Continue" (r.walletID == some walletID && !r.onboarding.busy &&
    contains sheet "Verification report" && contains sheet "Continue" && !contains sheet "Import and verify")
  check "restore: the report says verification waits for peers" (report == Real.verificationWaitingText && contains sheet report) report
  let (r, _) ← sh.tap .finishOnboarding r
  check "restore: Continue opens the wallet" (r.stage == .ready && r.sheets.isEmpty)
  let (r, _) ← sh.tap (.setAdvanced true) r
  let (r, _) ← sh.tap (.selectTab 2) r
  let (r, _) ← sh.tap (.backup .reveal) r
  check "restore: the new phone shows the same twelve words" (r.topSheet == some .revealPhrase && r.reveal.words == expected)
  backendRef.set backend
  rootDir.set (root / "screens-alice").toString

/-- The screen flows, in one directory. -/
def screens (root : System.FilePath) : IO Unit := do
  failuresReachTheirScreens
  settingsScreen root
  let (alice, aliceID) ← screenPhone root "screens-alice" 0xA1
  let (bob, _) ← screenPhone root "screens-bob" 0xB2
  let cardB ← bob.ownCard "Bob"
  let bobAddress ← bob.receiveAddress false
  let otherAddress ← bob.receiveAddress true
  let funder ← bob.receiveAddress true
  backendRef.set alice
  rootDir.set (root / "screens-alice").toString
  let sh ← Shell.new
  receiveScreen sh alice aliceID
  let (_, robertID) ← peopleScreens sh alice aliceID cardB otherAddress
  cardsRefusedOnTheAddPersonSheet sh aliceID
  homeScreens sh alice aliceID robertID bobAddress (← alice.receiveAddress false) funder
  backupScreens sh root alice aliceID 0xA1
  backendRef.set Backend.pending

/-- The explorer and manual-peer rules against what Foundation and the Swift app answered
(`FoundationVectors`, from `scripts/foundation-vectors`): a custom explorer's host, which strings
`explorerBaseURL` keeps (HTTPS anywhere, plain HTTP only on loopback) and how it spells them, the
transaction link under it, and `parsePeer`. -/
def foundationURLRules : IO Unit := do
  let txid := String.join (List.replicate 32 "ab")
  for (s, host, base, tx) in FoundationVectors.urls do
    check s!"url host: {repr s}" (urlHost s == host) s!"{urlHost s}"
    let got := explorerBaseURL .custom s .signet
    check s!"explorer base: {repr s}" (got == base) got
    let link := appendPath got ["tx", txid]
    check s!"transaction link: {repr s}" (link == tx) link
  -- where the app refuses what Foundation accepts: a non-ASCII host (Foundation applies IDNA)
  check "url host: non-ASCII host refused" (urlHost "https://münchen.de" == none)
  check "explorer base: non-ASCII host falls back to the preset"
    (explorerBaseURL .custom "https://münchen.de" .signet == "https://mempool.space/signet")
  for (text, want) in FoundationVectors.peers do
    let got := (parsePeer text).toOption
    check s!"peer: {repr text}" (got == want) s!"{got}"
    check s!"saved peer dials as validated: {repr text}"
      ((Real.parsePeerEndpoint text).map (·.description) == want)

/-! ## Background tasks through `perform` (#68)

iOS launches a task with a system event and expires it with another; the simulator refuses
`bgtask.schedule`, so outside a phone (LeanNative/leannative#22) only this runs them. Each case sends the
shell's event through `system`, the Model and the app's own `perform`, against a shell that records what it
is asked and a backend whose check the case decides, and reads the `bgtask.complete` the shell gets. The
deadline is a manual one (`backgroundDeadline`) that records each run's budget and that the case fires. -/

/-- The shell, for background tasks: what it is asked, each with whether the backend's check had drained
by then. -/
structure TaskShell where
  asked : IO.Ref (Array (String × Lean.Json × Bool))
  drained : IO.Ref Bool

def TaskShell.new : IO TaskShell := do return { asked := ← IO.mkRef #[], drained := ← IO.mkRef true }

def TaskShell.fx (s : TaskShell) : LeanNative.Native.Effects Host where
  post _ := pure ()
  cap _ _ _ := pure ()
  ask name args := do
    let drained ← s.drained.get
    s.asked.modify (·.push (name, args, drained))
    return Task.pure (Lean.Json.mkObj [("ok", Lean.Json.bool true)])

/-- The `bgtask.complete`s so far: the task, its `success`, and whether the check had drained. -/
def TaskShell.completions (s : TaskShell) : IO (Array (String × Option Bool × Bool)) := do
  return (← s.asked.get).filterMap fun (n, a, d) =>
    if n == "bgtask.complete" then some ((a.getObjValAs? String "id").toOption.getD "", (a.getObjValAs? Bool "success").toOption, d)
    else none

/-- The completions once the first has come and a later one has had time to follow. -/
def TaskShell.settled (s : TaskShell) : IO (Array (String × Option Bool × Bool)) := do
  discard <| waitUntil 5_000 (every := 2) do return !(← s.completions).isEmpty
  IO.sleep 150
  s.completions

/-- The shell's system event `{key: {id, kind}}` through `system`, the Model and `perform`. -/
def TaskShell.event (s : TaskShell) (key id kind : String) (m : Model) : IO Model := do
  let some h := system (Lean.Json.mkObj [(key, Lean.Json.mkObj [("id", Lean.Json.str id), ("kind", Lean.Json.str kind)])])
    | throw (IO.userError s!"{key} is not a system event")
  let (m, cs) := onHost h m
  for c in cs do WinnowApp.perform c s.fx
  return m

/-- The backend's background check as a case decides it: its result, and whether it holds until asked to
stop and then released (`gate`), as the real check drains its networking. -/
structure TaskCheck where
  result : Except String Bool
  holds : Bool
  runs : IO.Ref (Array String)
  cancels : IO.Ref Nat
  gate : IO.Promise Unit

def TaskCheck.new (result : Except String Bool) (holds := false) : IO TaskCheck := do
  return { result, holds, runs := ← IO.mkRef #[], cancels := ← IO.mkRef 0, gate := ← IO.Promise.new }

def TaskCheck.backend (c : TaskCheck) (sh : TaskShell) : Backend :=
  { Backend.pending with
    runBackgroundSync := fun s => do
      c.runs.modify (·.push s.network.name)
      sh.drained.set false
      if c.holds then
        while (← c.cancels.get) == 0 || !(← c.gate.isResolved) do IO.sleep 2
      sh.drained.set true
      match c.result with
      | .ok done => return done
      | .error e => throw (IO.userError e)
    cancelBackgroundSync := c.cancels.modify (· + 1) }

/-- #68: a background task's launch and expiry through `perform`: the budget for its kind, and exactly one
`bgtask.complete` under its id with the run's success, whether the check finishes, falls short, fails, or
is expired by iOS or its budget, when iOS expires it after it completed, when iOS launches it again while
it runs (the older check stops and drains before the newer runs), and when iOS expires it before it
started. -/
def backgroundTaskCommands : IO Unit := do
  let budgets ← IO.mkRef (#[] : Array (Nat × IO Unit))
  backgroundDeadline.set fun ms => do
    let (d, fire) ← LeanNative.Native.BackgroundRun.Deadline.manual
    budgets.modify (·.push (ms, fire))
    return d
  let refresh := Real.backgroundRefreshID
  let processing := Real.backgroundProcessingID
  let asleep : Model := { readyModel "w" with active := false }
  let start (result : Except String Bool) (holds := false) : IO (TaskShell × TaskCheck) := do
    let sh ← TaskShell.new
    let c ← TaskCheck.new result holds
    backendRef.set (c.backend sh)
    budgets.set #[]
    return (sh, c)
  let started (c : TaskCheck) : IO Bool := waitUntil 2_000 (every := 2) do return (← c.runs.get).size == 1
  -- a refresh that reaches the tip
  let (sh, c) ← start (.ok true)
  discard <| sh.event "bgtask" refresh "refresh" asleep
  let done ← sh.settled
  let schedules := (← sh.asked.get).filterMap fun (n, a, _) =>
    if n == "bgtask.schedule" then some ((a.getObjValAs? String "id").toOption, (a.getObjValAs? String "kind").toOption) else none
  check "refresh task: asks iOS for the next checks, one of each" (schedules.size == 2 &&
    schedules.contains (some refresh, some "refresh") && schedules.contains (some processing, some "processing"))
  check "refresh task: the check runs once, on the wallet's network" ((← c.runs.get) == #["regtest"])
  check "refresh task: 25 s to run" ((← budgets.get).map (·.1) == #[25_000])
  check "refresh task: completed once, successfully, under iOS's id" (done == #[(refresh, some true, true)]) (reprStr done)
  check "refresh task: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- a processing task whose check falls short of the tip
  let (sh, c) ← start (.ok false)
  discard <| sh.event "bgtask" processing "processing" asleep
  let done ← sh.settled
  check "processing task: 120 s to run" ((← budgets.get).map (·.1) == #[120_000])
  check "processing task: short of the tip, completed once, unsuccessfully"
    (done == #[(processing, some false, true)] && (← c.runs.get).size == 1) (reprStr done)
  -- a check that fails
  let (sh, _) ← start (.error "the peer hung up")
  discard <| sh.event "bgtask" refresh "refresh" asleep
  let done ← sh.settled
  check "failed check: completed once, unsuccessfully" (done == #[(refresh, some false, true)]) (reprStr done)
  -- iOS expires it while it runs, twice: the check is stopped once and drains before the completion
  let (sh, c) ← start (.ok true) (holds := true)
  let m ← sh.event "bgtask" processing "processing" asleep
  check "expired while running: the check started" (← started c)
  let m ← sh.event "bgtaskExpired" processing "processing" m
  discard <| sh.event "bgtaskExpired" processing "processing" m
  IO.sleep 50
  check "expired while running: the backend is asked to stop, once" ((← c.cancels.get) == 1)
  check "expired while running: nothing completes until the check drains" (← sh.completions).isEmpty
  c.gate.resolve ()
  let done ← sh.settled
  check "expired while running: completed once, unsuccessfully, after the check drained"
    (done == #[(processing, some false, true)]) (reprStr done)
  check "expired while running: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- the budget runs out: the deadline perform armed expires the run
  let (sh, c) ← start (.ok true) (holds := true)
  discard <| sh.event "bgtask" refresh "refresh" asleep
  check "budget spent: the check started" (← started c)
  let some (ms, fire) := (← budgets.get)[0]? | throw (IO.userError "no deadline was armed")
  check "budget spent: a refresh's 25 s" (ms == 25_000)
  fire
  IO.sleep 50
  check "budget spent: the backend is asked to stop" ((← c.cancels.get) == 1 && (← sh.completions).isEmpty)
  c.gate.resolve ()
  let done ← sh.settled
  check "budget spent: completed once, unsuccessfully" (done == #[(refresh, some false, true)]) (reprStr done)
  -- iOS's expiry comes after the check completed: the task has had its one answer
  let (sh, _) ← start (.ok true)
  let m ← sh.event "bgtask" processing "processing" asleep
  let done ← sh.settled
  check "expired after it completed: completed once, successfully" (done == #[(processing, some true, true)]) (reprStr done)
  discard <| sh.event "bgtaskExpired" processing "processing" m
  IO.sleep 50
  let done ← sh.completions
  check "expired after it completed: the late expiry answers nothing" (done == #[(processing, some true, true)]) (reprStr done)
  -- iOS launches the task again while its check still runs (the shell has ended the first): the older
  -- check is stopped and drains, the newer one runs after it and answers the shell, once, with its own result
  let (sh, c) ← start (.ok true) (holds := true)
  let m ← sh.event "bgtask" refresh "refresh" asleep
  check "launched again: the first check started" (← started c)
  discard <| sh.event "bgtask" refresh "refresh" m
  IO.sleep 50
  check "launched again: the older check is asked to stop, once" ((← c.cancels.get) == 1)
  check "launched again: the newer check waits for the older to drain"
    ((← c.runs.get).size == 1 && (← sh.completions).isEmpty)
  check "launched again: one run registered under the id"
    (((← WinnowApp.backgroundRuns.get).filter (·.1 == refresh)).length == 1)
  c.gate.resolve ()
  let done ← sh.settled
  check "launched again: the newer check runs once the older drained" ((← c.runs.get).size == 2)
  check "launched again: completed once, by the newer run, successfully" (done == #[(refresh, some true, true)]) (reprStr done)
  check "launched again: each launch its 25 s" ((← budgets.get).map (·.1) == #[25_000, 25_000])
  check "launched again: nothing left running" (← WinnowApp.backgroundRuns.get).isEmpty
  -- launched during boot: it waits for the wallet, then runs
  let (sh, c) ← start (.ok true)
  let m ← sh.event "bgtask" refresh "refresh" {}
  check "launched during boot: waits for the wallet" (m.pendingBackgroundTask.isSome && (← c.runs.get).isEmpty)
  let (_, cs) := onHost (.booted 0 (.opened "w")) m
  for cmd in cs.filter (· matches .runBackgroundTask ..) do WinnowApp.perform cmd sh.fx
  let done ← sh.settled
  check "launched during boot: runs once the wallet opens, completes once"
    (done == #[(refresh, some true, true)] && (← c.runs.get).size == 1) (reprStr done)
  -- expired before it started: iOS's time ran out while the app was still booting
  let (sh, c) ← start (.ok true)
  let m ← sh.event "bgtask" refresh "refresh" {}
  let m ← sh.event "bgtaskExpired" refresh "refresh" m
  let m ← sh.event "bgtaskExpired" refresh "refresh" m
  let done ← sh.settled
  check "expired before it started: completed once, unsuccessfully, however often iOS says so"
    (done == #[(refresh, some false, true)]) (reprStr done)
  let (_, cs) := onHost (.booted 0 (.opened "w")) m
  check "expired before it started: boot does not run it, no check ran"
    (!cs.any (· matches .runBackgroundTask ..) && (← c.runs.get).isEmpty && (← budgets.get).isEmpty)
  backgroundDeadline.set fun ms => pure (.after ms)
  backendRef.set Backend.pending

/-- #68: test mode pins the seed one way, `WINNOW_E2E_ENTROPY`. A run that sets only Swift's
`WINNOW_E2E_MNEMONIC`, or entropy that is not hex, stops rather than create a real seed. -/
def testModeSeed : IO Unit := do
  let resolve (vars : List (String × String)) := WinnowApp.E2E.resolve fun k => ((("WINNOW_E2E", "1") :: vars).lookup k)
  check "test mode: WINNOW_E2E_ENTROPY pins the seed"
    (match resolve [("WINNOW_E2E_ENTROPY", "000102030405060708090a0b0c0d0e0f")] with
     | .active m => m.entropy.map (·.toList) == some ((List.range 16).map (·.toUInt8))
     | _ => false)
  check "test mode: a recovery phrase alone pins nothing"
    (resolve [("WINNOW_E2E_MNEMONIC", "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about")]
      matches .missingPinnedEntropy)
  check "test mode: entropy that is not hex pins nothing" (resolve [("WINNOW_E2E_ENTROPY", "abandon")] matches .missingPinnedEntropy)
  check "test mode: nothing set pins nothing" (resolve [] matches .missingPinnedEntropy)
  check "test mode: the launch reads one seed variable"
    (WinnowApp.e2eVariables.filter (fun v => v == "WINNOW_E2E_ENTROPY" || v == "WINNOW_E2E_MNEMONIC") == ["WINNOW_E2E_ENTROPY"])

def main : IO UInt32 := runMain "records-test" do
  let root ← IO.FS.createTempDir
  IO.println s!"records-test in {root}"
  syncErrorBookkeeping
  foundationURLRules
  peerGatewayModel
  syncBookkeepingScreens
  backgroundRuns
  backgroundTaskCommands
  testModeSeed
  try
    let a ← newPhone root "A"
    let b ← newPhone root "B"
    peopleAndPastes a b
    receiveLabels a b
    lookupSenderTest b
    let before ← a.records
    tamper root a
    reopenFromDisk a before
    paymentIndexAndPayTo a b
    sealFailures root
    screens root
  catch e =>
    check "the script ran to the end" false (toString e)
