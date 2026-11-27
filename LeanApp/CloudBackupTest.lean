import WinnowApp.Real.CloudAppState
import WinnowApp.Real
import WinnowApp.View
import WinnowApp.E2E
import WinnowApp.Main
import LeanNative.Erase
import LeanNative.Json
import Lean.Data.Json
import TestKit.Check
import TestKit.Fixtures
import TestKit.Regtest
import AppTestNames

/-! `cloud-backup-test`: the encrypted iCloud recovery formats, headless.

* upstream d2ca878's `CloudWalletBackupTests` (all six), `CloudAppStateTests` (all three) and the restore
  halves of `CloudBackupTests` (what a backup restores, and the digest an automatic update compares);
  the controller around them (iCloud Keychain, CloudKit, scheduling) needs the shell and is not here;
* `../Lean/Vectors/cloud-backup.json`, written by upstream's `CloudWalletBackup.swift` (verbatim, over a
  copy of d2ca878's WalletCore): its version 1 and version 2 backups open here, its `wallet-…` purposes
  and the backup digest (and the canonical JSON under it) match byte for byte;
* the app's device check before the iCloud backup (`declinedDeviceCheck`, #68), over a fake shell.

`--write <dir>` also leaves a Lean-made backup (`lean-backup.json`) and its key (`lean-backup.key`) there for
the Swift side to open. Run from `LeanApp/`. Exits 1 on any failure. -/

open Winnow WinnowApp WinnowApp.RecordsReal Keys TestKit
open TestKit.Regtest (waitUntil)
open Tx (BitcoinNetwork)

instance : Describe RecordsError := ⟨(·.name), fun e => s!"{e.name}: {e.description}"⟩

def refusedW {α} (x : WM α) : IO Bool := do return (← x.run).toOption.isNone
def refusedR {α} (x : RM α) : IO Bool := do return (← x.run).toOption.isNone

def newKeys : IO (KeyStore IO) := do return inMemoryKeyStore (← IO.mkRef {})

def walletBundle (network : BitcoinNetwork) (fill : UInt8) : TM ImportBundle := do
  let w ← need "create" (Wallet.create network (← newKeys) none (some (ByteArray.mk (Array.replicate 16 fill))) 100)
  need "export" (w.exportBundle (includeMnemonic := true))

def randomKey : IO ByteArray := IO.getRandomBytes 32

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

def jsonOf (b : CloudWalletBackup) : TM Lean.Json := do
  let text := String.fromUTF8! (← need "encode" b.encoded)
  match Lean.Json.parse text with | .ok j => pure j | .error e => throw e

def bytesOfJson (j : Lean.Json) : ByteArray := j.compress.toUTF8

/-! ## CloudWalletBackupTests -/

def roundTripRestoresSigningAndAddressCounters : TM Unit := do
  let original := { (← walletBundle .signet 7) with nextReceiveIndex := some 19, nextChangeIndex := some 8 }
  let key ← randomKey
  let encrypted ← need "create" (CloudWalletBackup.create original key)
  let data ← need "encode" encrypted.encoded
  check "round trip: the file does not hold the words" (!contains (String.fromUTF8! data) original.mnemonic.get!)
  let restored ← need "restore" ((← need "decode" (CloudWalletBackup.decode data)).restoredBundle key)
  check "round trip: the bundle comes back whole" (restored == original)
  let keys ← newKeys
  let wallet ← need "import" (Wallet.importing restored keys)
  check "round trip: importing it stores the words" (match ← (keys.load wallet.id).run with
    | .ok s => s == .mnemonic original.mnemonic.get! | .error _ => false)

def automaticUpdateKeepsTheSealedKeyAndNewHistoryFrontier : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  let first ← need "create" (CloudWalletBackup.create original key)
  let next := { original with mnemonic := none, lastKnownHeight := 123, nextReceiveIndex := some 5 }
  let updated ← need "update" (first.updating next key)
  check "update: the phrase box is kept" (updated.sealedPhrase == first.sealedPhrase)
  let restored ← need "restore" (updated.restoredBundle key)
  check "update: the words, the new frontier and the new cursor"
    (restored.mnemonic == original.mnemonic && restored.lastKnownHeight == 123 && restored.nextReceiveIndex == some 5)

def wrongKeyAndModifiedMetadataAreRejected : TM Unit := do
  let key ← randomKey
  let original ← walletBundle .signet 7
  let backup ← need "create" (CloudWalletBackup.create original key)
  check "tamper: a wrong key" (← refusedW (backup.restoredBundle (← randomKey)))
  let json ← jsonOf backup
  let zeros := Base64.encode (ByteArray.mk (Array.replicate 40 0))
  for (field, value) in [("id", Lean.Json.str (← UUIDText.random)), ("network", .str "mainnet"), ("savedAt", (1 : Nat)),
                         ("sealedWallet", .str zeros), ("sealedPhrase", .str zeros)] do
    let changed := bytesOfJson (json.setObjVal! field value)
    check s!"tamper: a changed {field} is refused"
      (← refusedW (do (← CloudWalletBackup.decode changed).restoredBundle key))
  check "tamper: version 3 does not decode" (← refusedW (CloudWalletBackup.decode (bytesOfJson (json.setObjVal! "version" (3 : Nat)))))

def appContextIsEncryptedAndUpdatesWithoutReadingThePhrase : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  let metadata := "private contact and invoice label".toUTF8
  let first ← need "create" (CloudWalletBackup.create original key (appState := some metadata))
  check "app data: not in the clear" (!contains (String.fromUTF8! (← need "encode" first.encoded)) "invoice label")
  check "app data: restored" ((← need "app state" (first.restoredAppState key)) == some metadata)
  let publicBundle := { original with mnemonic := none }
  let edited := "edited local notes".toUTF8
  let second ← need "update" (first.updating publicBundle key (appState := some edited))
  check "app data: the phrase box is kept" (second.sealedPhrase == first.sealedPhrase)
  check "app data: replaced" ((← need "app state" (second.restoredAppState key)) == some edited)
  check "app data: the bundle is unchanged" ((← need "restore" (second.restoredBundle key)) == original)
  check "app data: past 10 MiB is refused"
    (← refusedW (first.updating publicBundle key
      (appState := some (ByteArray.mk (Array.replicate (CloudWalletBackup.maximumAppStateBytes + 1) 0)))))

/-- A version 1 backup as upstream's test makes it (the bundle's `serialized()` text sealed alone). -/
def legacyBackup (original : ImportBundle) (key : ByteArray) (id : String) (savedAt : Float) : TM CloudWalletBackup := do
  let ctx (purpose : String) := CloudWalletBackup.context id original.network purpose
  let sealWith (pt aad : ByteArray) : TM ByteArray := do
    match ← AESGCM.sealRandom key pt aad with
    | .ok b => pure b.combined.get!
    | .error e => throw e.name
  let publicBundle := { original with mnemonic := none }
  let phrase ← sealWith original.mnemonic.get!.toUTF8 (ctx "phrase")
  let wallet ← sealWith publicBundle.serialized.toUTF8 (ctx (CloudWalletBackup.walletPurpose savedAt))
  return { version := 1, id, network := original.network, savedAt, sealedPhrase := phrase, sealedWallet := wallet }

def legacyBackupRestoresAndUpgradesWithoutLosingItsKey : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  -- Date(timeIntervalSince1970: 1_700_000_000)
  let legacy ← legacyBackup original key (← UUIDText.random) (1_700_000_000 - 978_307_200)
  let loaded ← need "decode" (CloudWalletBackup.decode (← need "encode" legacy.encoded))
  check "legacy: restores" ((← need "restore" (loaded.restoredBundle key)) == original)
  check "legacy: has no app data" ((← need "app state" (loaded.restoredAppState key)) == none)
  let upgraded ← need "upgrade" (loaded.updating { original with mnemonic := none } key (appState := some "notes".toUTF8))
  check "legacy: upgrades to version 2 with its phrase box" (upgraded.version == 2 && upgraded.sealedPhrase == legacy.sealedPhrase)
  check "legacy: the upgrade restores" ((← need "restore" (upgraded.restoredBundle key)) == original &&
    (← need "app state" (upgraded.restoredAppState key)) == some "notes".toUTF8)
  let downgraded := bytesOfJson ((← jsonOf upgraded).setObjVal! "version" (1 : Nat))
  check "legacy: a version 2 box called version 1 does not restore"
    (← refusedW (do (← CloudWalletBackup.decode downgraded).restoredBundle key))

def mismatchedWalletAndMissingPhraseAreRefused : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  let backup ← need "create" (CloudWalletBackup.create original key)
  let other := { original with descriptor := some "different wallet" }
  check "mismatch: another wallet does not update it" (← refusedW (backup.updating other key))
  check "mismatch: no words, no backup" (← refusedW (CloudWalletBackup.create { other with mnemonic := none } key))
  check "mismatch: past 32 MiB does not decode"
    (← refusedW (CloudWalletBackup.decode (ByteArray.mk (Array.replicate (CloudWalletBackup.maximumBytes + 1) 0))))

/-! ## CloudBackupTests (the restore halves) -/

def cloudBackupRestores : TM Unit := do
  let bundle ← walletBundle .signet 9
  let key ← randomKey
  let first ← need "enable" (CloudWalletBackup.create bundle key (appState := some "before".toUTF8))
  let watchOnly := { bundle with mnemonic := none }
  let before : CloudBackupContents := { bundle := watchOnly, appState := some "before".toUTF8 }
  let after : CloudBackupContents := { bundle := watchOnly, appState := some "after".toUTF8 }
  check "contents: only changing the app data changes the digest" (before.digest != after.digest)
  check "contents: the words are not part of the digest"
    (({ before with bundle := bundle } : CloudBackupContents).digest == before.digest)
  let second ← need "update" (first.updating watchOnly key (appState := after.appState))
  check "contents: the app data and the whole bundle restore"
    ((← need "app state" (second.restoredAppState key)) == some "after".toUTF8 &&
     (← need "restore" (second.restoredBundle key)) == bundle)

/-! ## CloudAppStateTests -/

structure Fixture where
  bundle : ImportBundle
  state : CloudAppState
  dir : System.FilePath

def fixture : TM Fixture := do
  let dir ← IO.FS.createTempDir
  let bundle ← walletBundle .mainnet 8
  let payTo ← match PersonPayTo.ofAddress "1BoatSLRHtKNngkdXEeobR76b53LETtpyT" .mainnet with
    | .ok p => pure p | .error e => throw e
  let person : PersonRecord := { id := ← UUIDText.random, name := "Saved friend", payTo := some payTo, nextPaymentIndex := 17 }
  let script ← match AddressDecoder.scriptPubKey "1BoatSLRHtKNngkdXEeobR76b53LETtpyT" .mainnet with
    | .ok s => pure s | .error _ => throw "script"
  let state : CloudAppState := {
    network := bundle.network, descriptor := bundle.descriptor,
    people := { people := #[person], senderByTxid := #[(String.join (List.replicate 32 "01"), person.id)] },
    receiveLabels := #[(hex script, "Private invoice")], ownDisplayName := "Me", advancedMode := true }
  return { bundle, state, dir }

def cloudContextRoundTrips : TM Unit := do
  let f ← fixture
  let restored ← match ← need "decode" (CloudAppState.decode (some f.state.encoded) f.bundle) with
    | some r => pure r | none => throw "no context"
  check "context: round trips" (restored == f.state)
  let vault := StoreKeyVault.inMemory (← IO.mkRef {})
  let (people, _) ← PeopleStore.configure vault (some (f.dir / "people.json")) .mainnet
  let plan ← need "plan" (people.planRestore restored.people)
  let people ← need "restore" (people.restore vault writeAtomically plan)
  check "context: the address book restores" ((← need "backup" people.backup) == f.state.people)
  let labels ← LabelStore.open (some (f.dir / "labels.json")) "restored" .mainnet
  let labels ← need "labels restore" (labels.restore writeAtomically restored.receiveLabels)
  let sorted (xs : Array (String × String)) := (xs.toList.mergeSort fun a b => !(b.1 < a.1)).toArray
  check "context: the receive notes restore" (sorted (← need "labels backup" labels.backup) == sorted f.state.receiveLabels)
  let reopened ← LabelStore.open (some (f.dir / "labels.json")) "restored" .mainnet
  check "context: the receive notes are on disk" (sorted (← need "reopened" reopened.backup) == sorted f.state.receiveLabels)
  check "context: the manual export stays without the address book" (!contains f.bundle.serialized "Saved friend")
  check "context: older backups have none" ((← need "none" (CloudAppState.decode none f.bundle)).isNone)

def existingContactsAndNewerPaymentCounterSurviveRestore : TM Unit := do
  let f ← fixture
  let vault := StoreKeyVault.inMemory (← IO.mkRef {})
  let (store, _) ← PeopleStore.configure vault (some (f.dir / "people.json")) .mainnet
  let p := f.state.people.people[0]!
  let mine : PeopleStore.Backup :=
    { people := #[{ p with id := ← UUIDText.random, name := "Current local name", nextPaymentIndex := 24 }], senderByTxid := #[] }
  let store ← need "restore local" (store.restore vault writeAtomically mine)
  let merged ← need "plan" (store.planRestore f.state.people)
  check "merge: one person, by key" (merged.people.size == 1)
  check "merge: the local name stays" (merged.people[0]!.name == "Current local name")
  check "merge: the newer counter stays" (merged.people[0]!.nextPaymentIndex == 24)
  check "merge: the sender label moves to the local id" ((merged.senderByTxid.map (·.2)) == #[mine.people[0]!.id])

def wrongNetworkOrMalformedLabelsAreRejectedBeforeStoreChanges : TM Unit := do
  let f ← fixture
  let json ← match Lean.Json.parse (String.fromUTF8! f.state.encoded) with | .ok j => pure j | .error e => throw e
  let signet := json.setObjVal! "network" "signet"
  check "context: another network is refused" (← refusedR (CloudAppState.decode (some (bytesOfJson signet)) f.bundle))
  let badLabels := (signet.setObjVal! "network" "mainnet").setObjVal! "receiveLabels" (Lean.Json.mkObj [("not a script", "Private note")])
  check "context: a malformed note is refused" (← refusedR (CloudAppState.decode (some (bytesOfJson badLabels)) f.bundle))
  let vault := StoreKeyVault.inMemory (← IO.mkRef {})
  let (store, _) ← PeopleStore.configure vault (some (f.dir / "people.json")) .mainnet
  let store ← need "restore" (store.restore vault writeAtomically f.state.people)
  let invalid := { f.state.people with
    senderByTxid := f.state.people.senderByTxid.push (String.join (List.replicate 32 "02"), "unknown person") }
  check "context: a dangling sender name fails validation" (← refusedR (store.planRestore invalid))
  check "context: the store is unchanged" ((← need "backup" store.backup) == f.state.people)

/-! ## Swift's own output (`Vectors/cloud-backup.json`) -/

def swiftVectors (writeDir : Option String) : TM Unit := do
  let text ← IO.FS.readFile "../Lean/Vectors/cloud-backup.json"
  let j ← match Lean.Json.parse text with | .ok j => pure j | .error e => throw e
  let str (k : String) : TM String := match j.getObjValAs? String k with | .ok s => pure s | .error e => throw e
  let bundle ← match ImportBundle.decode (← str "bundle") with | .ok b => pure b | .error e => throw e.name
  let key := ofHex! (← str "key")
  let appState := ofHex! (← str "appState")
  let v2 ← need "swift v2" (CloudWalletBackup.decode (← str "v2").toUTF8)
  check "swift v2: restores the bundle" ((← need "restore" (v2.restoredBundle key)) == bundle)
  check "swift v2: restores the app data" ((← need "app state" (v2.restoredAppState key)) == some appState)
  check "swift v2: savedAt and the id read back" (v2.savedAt == 783_000_000.123456 && (UUIDText.canonical? v2.id) == some v2.id)
  let plain ← need "swift v2 plain" (CloudWalletBackup.decode (← str "v2NoAppState").toUTF8)
  check "swift v2 without app data" ((← need "restore" (plain.restoredBundle key)) == bundle &&
    (← need "app state" (plain.restoredAppState key)).isNone)
  let v1 ← need "swift v1" (CloudWalletBackup.decode (← str "v1").toUTF8)
  check "swift v1: restores" (v1.version == 1 && (← need "restore" (v1.restoredBundle key)) == bundle &&
    (← need "app state" (v1.restoredAppState key)).isNone)
  let dates ← match j.getObjValAs? (Array Float) "referenceDates" with | .ok d => pure d | .error e => throw e
  let purposes ← match j.getObjValAs? (Array String) "walletPurposes" with | .ok d => pure d | .error e => throw e
  for (d, p) in dates.zip purposes do
    check s!"swift purpose for {d}: {p}" (CloudWalletBackup.walletPurpose d == p) (CloudWalletBackup.walletPurpose d)
  let plainContents : CloudBackupContents := { bundle }
  let withApp : CloudBackupContents := { bundle, appState := some appState }
  check "swift digest without app data" (hex plainContents.digest == (← str "digestWithoutAppState"))
  check "swift digest with app data" (hex withApp.digest == (← str "digestWithAppState"))
  check "swift canonical contents JSON, byte for byte"
    (SwiftJSON.write ({ withApp with bundle := { bundle with mnemonic := none } }).toJV == (← str "contentsJSON"))
  -- A Lean-made backup of the same bundle for Swift to open.
  if let some dir := writeDir then
    let mine ← need "create" (CloudWalletBackup.create bundle key (appState := some appState))
    IO.FS.writeBinFile (System.FilePath.mk dir / "lean-backup.json") (← need "encode" mine.encoded)
    IO.FS.writeFile (System.FilePath.mk dir / "lean-backup.key") (hex key)
    IO.println s!"  wrote {dir}/lean-backup.json"

/-! ## CloudBackupTests: the controller (memory store and keys for CloudKit and iCloud Keychain) -/

structure CtlFixture where
  controller : Real.CloudBackupController
  cloud : Real.MemoryCloud
  bundle : ImportBundle
  dir : System.FilePath

open Real in
def ctlFixture : TM CtlFixture := do
  let cloud ← MemoryCloud.new
  let controller ← CloudBackupController.new cloud.store (← memoryCloudKeys) (scheduleDelayMs := 50)
  let dir ← IO.FS.createTempDir
  let w ← need "create" (Wallet.create .signet (← newKeys) none (some (ByteArray.mk (Array.replicate 16 9))) 100)
  controller.configure (some dir) (some "test-wallet")
  return { controller, cloud, bundle := ← need "export" (w.exportBundle (includeMnemonic := true)), dir }

def failsWith {α} (x : IO α) (text : String) : IO Bool := do
  match ← x.toBaseIO with
  | .ok _ => return false
  | .error e => return toString e == text

def fails {α} (x : IO α) : IO Bool := do return (← x.toBaseIO) matches .error _

def cloudOk {α} (x : Real.CloudM α) : TM α := ExceptT.mk do
  match ← x.run with
  | .ok a => pure (.ok a)
  | .error e => pure (.error e.description)

def cloudFails {α} (x : Real.CloudM α) : IO Bool := do return (← x.run) matches .error _

def cloudFailsWith {α} (x : Real.CloudM α) (expected : Real.CloudError) : IO Bool := do
  match ← x.run with
  | .ok _ => return false
  | .error e => return e == expected

private def exceptEq [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

open Real in
def controllerTests : TM Unit := do
  -- testNoUploadUntilPreparedAndStopKeepsCloudCopy
  let f ← ctlFixture
  let asked ← IO.mkRef false
  cloudOk <| f.controller.update (do asked.set true; return { bundle := f.bundle })
  check "no upload until prepared" (!(← asked.get) && (← f.cloud.count) == 0)
  cloudOk <| f.controller.enable f.bundle (walletID := "test-wallet")
  check "enabled once prepared" (← f.controller.get).enabled
  cloudOk <| f.controller.stop
  check "stop keeps the iCloud copy" (!(← f.controller.get).enabled && (← f.cloud.count) == 1)
  check "stop sets statusTitle to Off with no error issue" ((← f.controller.get).statusTitle == "Off" && (← f.controller.get).issue.isNone)
  -- testFailedUploadKeepsLastSuccessfulBackup
  let f ← ctlFixture
  cloudOk <| f.controller.enable f.bundle (walletID := "test-wallet")
  let saved := (← f.controller.get).lastSaved
  f.cloud.failing.set true
  let updated := { f.bundle with mnemonic := none, nextReceiveIndex := some 7 }
  check "a failed upload is not treated as saved" (← cloudFailsWith (f.controller.update (pure { bundle := updated })) (.issue .offline))
  check "the last successful save stays" ((← f.controller.get).lastSaved == saved)
  f.cloud.failing.set false
  f.controller.discover "signet"
  match (← f.controller.get).available[0]? with
  | some b => check "the last successful backup restores" ((← cloudOk (f.controller.restore b.id)) == f.bundle)
  | none => check "the backup is listed" false
  -- testReconfigureSameWalletDoesNotCancelBackup
  let f ← ctlFixture
  f.controller.configure (some f.dir) (some "test-wallet")
  cloudOk <| f.controller.enable f.bundle (walletID := "test-wallet")
  f.controller.configure (some f.dir) (some "test-wallet")
  check "reconfiguring the same wallet keeps the backup" (← f.controller.get).enabled
  f.controller.configure (some f.dir) (some "another-wallet")
  check "another wallet has none" (!(← f.controller.get).enabled)
  -- testCancelledExportCannotUploadToAnotherWallet
  let f ← ctlFixture
  cloudOk <| f.controller.enable f.bundle (walletID := "test-wallet")
  let switched := f.controller.update do
    f.controller.configure (some f.dir) (some "another-wallet")
    return { bundle := { f.bundle with nextReceiveIndex := some 8 } }
  check "a wallet change cancels the export" (← cloudFailsWith switched .cancelled)
  check "nothing uploaded for the other wallet" ((← f.cloud.saves.get) == 1 && !(← f.controller.get).enabled)
  -- testChangedAccountCannotOverwriteExistingBackup
  let f ← ctlFixture
  cloudOk <| f.controller.enable f.bundle (walletID := "test-wallet")
  f.cloud.accountName.set "second-account"
  check "a changed account cannot overwrite the backup"
    (← cloudFailsWith (f.controller.update (pure { bundle := { f.bundle with nextReceiveIndex := some 6 } })) (.issue .accountChanged))
  check "one save only" ((← f.cloud.saves.get) == 1)
  -- testLateUploadCannotEnableBackupAfterWalletChange
  let f ← ctlFixture
  let gate ← IO.Promise.new
  f.cloud.hold.set (some gate)
  let enable ← IO.asTask ((f.controller.enable f.bundle (walletID := "test-wallet")).run)
  discard <| waitUntil 2000 (every := 10) f.cloud.holding.get
  f.controller.configure (some f.dir) (some "another-wallet")
  gate.resolve ()
  check "a late acknowledgement is cancelled" (match ← IO.wait enable with | .ok (.error .cancelled) => true | _ => false)
  check "it enables nothing" (!(← f.controller.get).enabled && (← f.controller.get).lastSaved.isNone)
  let reopened ← CloudBackupController.new f.cloud.store (← memoryCloudKeys)
  reopened.configure (some f.dir) (some "another-wallet")
  check "the encrypted retry does not configure a different wallet" (!(← reopened.get).enabled)
  -- testOnlyChangingAppContextStillUpdatesBackup
  let f ← ctlFixture
  cloudOk <| f.controller.enable f.bundle (some "before".toUTF8) "test-wallet"
  cloudOk <| f.controller.update (pure { bundle := { f.bundle with mnemonic := none }, appState := some "after".toUTF8 })
  check "the context alone changing uploads again" ((← f.cloud.saves.get) == 2)
  f.controller.discover "signet"
  match (← f.controller.get).available[0]? with
  | some b =>
    let r ← cloudOk (f.controller.restoreContents b.id)
    check "the new context restores" (r.contents.appState == some "after".toUTF8)
    check "with the words carried forward" (r.contents.bundle == f.bundle)
  | none => check "the backup is listed" false
  -- testRestoredDeviceResumesBackupsAcrossOfflineRelaunchWithoutOverwritingOriginal
  let f ← ctlFixture
  cloudOk <| f.controller.enable f.bundle (walletID := "test-wallet")
  f.controller.discover "signet"
  let some source := (← f.controller.get).available[0]? | throw "no backup listed"
  let restored ← cloudOk (f.controller.restoreContents source.id)
  let keys ← memoryCloudKeys
  let replacement := f.dir / "replacement"
  IO.FS.createDirAll replacement
  let device ← CloudBackupController.new f.cloud.store keys
  device.configure (some replacement) (some "test-wallet")
  cloudOk <| device.resume restored.contents "test-wallet" restored.account
  check "resume: enabled, not yet acknowledged" ((← device.get).enabled && (← device.get).lastSaved.isNone)
  f.cloud.failing.set true
  check "resume: an offline save fails" (← cloudFails (device.update (pure { bundle := f.bundle })))
  check "resume: still enabled, still not saved" ((← device.get).enabled && (← device.get).lastSaved.isNone)
  let relaunched ← CloudBackupController.new f.cloud.store keys
  relaunched.configure (some replacement) (some "test-wallet")
  check "resume: the retry survives a relaunch" ((← relaunched.get).enabled && (← relaunched.get).lastSaved.isNone)
  f.cloud.failing.set false
  cloudOk <| relaunched.update (pure { bundle := f.bundle })
  check "resume: saved once online" (← relaunched.get).lastSaved.isSome
  check "resume: the replacement phone has its own record" ((← f.cloud.count) == 2)
  check "resume: the original backup is untouched" ((← cloudOk (f.controller.restore source.id)) == f.bundle)
  -- testAutomaticDefaultAndOptOutSurviveRestartAndWalletChanges
  let f ← ctlFixture
  check "automatic by default, not backed up" ((← f.controller.get).automaticEnabled && (← f.controller.get).statusTitle == "Not backed up")
  cloudOk <| f.controller.prepare { bundle := f.bundle } "test-wallet"
  check "prepared: backing up" ((← f.controller.get).statusTitle == "Backing up")
  cloudOk <| f.controller.stop
  let reopened ← CloudBackupController.new f.cloud.store (← memoryCloudKeys)
  reopened.configure (some f.dir) (some "test-wallet")
  check "the opt-out survives a restart" (!(← reopened.get).automaticEnabled)
  cloudOk <| reopened.prepare { bundle := f.bundle } "test-wallet"
  check "an opted-out wallet prepares nothing" (!(← reopened.get).enabled)
  reopened.configure (some f.dir) (some "new-wallet")
  check "a new wallet is automatic" (← reopened.get).automaticEnabled
  reopened.configure (some f.dir) (some "test-wallet")
  check "the opted-out wallet stays off" (!(← reopened.get).automaticEnabled)
  cloudOk <| reopened.setAutomatic true
  check "turned on again, it needs preparation" (← reopened.get).needsPreparation
  -- testOfflineInitialPreparationDoesNotRequireAnAccountOrClaimSuccess
  let f ← ctlFixture
  f.cloud.failing.set true
  cloudOk <| f.controller.prepare { bundle := f.bundle } "test-wallet"
  check "offline preparation: enabled, not saved" ((← f.controller.get).enabled && (← f.controller.get).lastSaved.isNone)
  check "offline: the upload fails" (← cloudFails (f.controller.update (pure { bundle := f.bundle })))
  check "offline: still not saved" (← f.controller.get).lastSaved.isNone
  f.cloud.failing.set false
  cloudOk <| f.controller.update (pure { bundle := f.bundle })
  check "online: backed up" ((← f.controller.get).statusTitle == "Backed up")
  -- testScheduledFailuresBackOffWithoutDroppingAutomaticPreference
  let f ← ctlFixture
  cloudOk <| f.controller.prepare { bundle := f.bundle } "test-wallet"
  f.cloud.failing.set true
  f.controller.schedule (pure { bundle := f.bundle })
  discard <| waitUntil 8000 (every := 10) do return (← f.controller.get).issue.isSome
  let st ← f.controller.get
  check "a scheduled offline failure records offline issue" (st.issue == some .offline)
  check "transient offline keeps automatic preference and calm Waiting for connection title"
    (st.automaticEnabled && st.statusTitle == "Waiting for connection")
  check "the retry waits at least 50 s" (st.retryAfter - (← unixNowFloat) > 50)
  let retried ← IO.mkRef false
  f.controller.schedule (do retried.set true; return { bundle := f.bundle })
  IO.sleep 120
  check "a retry inside the backoff is not attempted" (!(← retried.get) && (← f.cloud.saveAttempts.get) == 1)
  f.controller.suspend
  -- testNewInstallationFindsBackupButWaitsForItsKey
  let f ← ctlFixture
  let shared ← memoryCloudKeys
  let original ← CloudBackupController.new f.cloud.store shared
  original.configure (some f.dir) (some "test-wallet")
  cloudOk <| original.enable f.bundle (walletID := "test-wallet")
  let waiting ← CloudBackupController.new f.cloud.store (← memoryCloudKeys)
  waiting.discover "signet"
  let some b := (← waiting.get).available[0]? | throw "no backup listed"
  check "a new installation waits for the key" (← cloudFailsWith (waiting.restore b.id) (.issue .keychainUnavailable))
  let later ← CloudBackupController.new f.cloud.store shared
  later.discover "signet"
  check "once the key arrives it restores" ((← cloudOk (later.restore b.id)) == f.bundle)
  check "restoring replaced nothing" ((← f.cloud.saves.get) == 1)

/-! ## AutomaticCloudBackupTests and the onboarding without a checklist (`WalletStartupTests`) -/

/-- A phone on a custom signet with an unreachable peer (test mode's fixture, as upstream's tests), iCloud
through memory versions. -/
structure CloudPhone where
  backend : Backend
  env : Real.Env
  app : Real.CloudApp
  cloud : Real.MemoryCloud
  keys : Keys.KeyStore IO
  dir : String
  settings : Settings
  authAttempts : IO.Ref Nat

open Real in
def cloudPhone (root : System.FilePath) (name : String) (keys : Keys.KeyStore IO) (auth : Bool) (cloud : Option MemoryCloud := none)
    (cloudKeys : Option CloudBackupKeys := none) (whileAuthenticating : IO Unit := pure ())
    (deviceCheck : Option (String → IO Unit) := none) (store : Option CloudBackupStore := none) : TM CloudPhone := do
  let vars := [("WINNOW_E2E", "1"), ("WINNOW_E2E_RUN", "cloud"), ("WINNOW_E2E_ENTROPY", "04040404040404040404040404040404"),
               ("WINNOW_E2E_PEER", "127.0.0.1:1"), ("WINNOW_E2E_CHALLENGE", "51")]
  let .active mode := WinnowApp.E2E.resolve (fun k => vars.lookup k) | throw "test mode did not resolve"
  let cloud ← match cloud with | some c => pure c | none => MemoryCloud.new
  let cloudKeys ← match cloudKeys with | some k => pure k | none => memoryCloudKeys
  let attempts ← IO.mkRef 0
  let deps : Deps := { keyStore := keys, networkParams := mode.networkParams, peerCount := 1, importPeerWaitMs := 1_000,
                       fetch := fun _ => throw (.other "offline") }
  let (backend, env, app) ← Backend.realWithCloud deps (store := store.getD cloud.store) (keys := cloudKeys)
    (authenticate := fun reason => do
      attempts.modify (· + 1)
      whileAuthenticating
      -- the app's own check over a scripted shell (`declinedDeviceCheck`), or `auth` as the answer
      match deviceCheck with
      | some check => check reason
      | none => unless auth do throw (IO.userError "Authentication was denied."))
    (scheduleDelayMs := 50)
  let dir := (root / name / "signet").toString
  IO.FS.createDirAll dir
  let settings : Settings := { network := .signet, signet := { manualPeers := ["127.0.0.1:1"] } }
  return { backend, env, app, cloud, keys, dir, settings, authAttempts := attempts }

/-- Boot with a wallet already on disk, scene active. -/
def CloudPhone.bootExisting (p : CloudPhone) : TM Unit := do
  discard <| need "create" (Wallet.create .signet p.keys (some (System.FilePath.mk p.dir / "wallet.json")) (some (ByteArray.mk (Array.replicate 16 4))))
  discard <| p.backend.openWallet .signet p.dir

def CloudPhone.activate (p : CloudPhone) : IO Unit := do
  p.backend.cloudScene true
  p.backend.startNetworking p.settings
  p.backend.cloudTick

def automaticCloudTests (root : System.FilePath) : TM Unit := do
  -- testDeclinedAuthenticationDoesNotRepeatWithinForegroundSession
  let p ← cloudPhone root "declined" (← newKeys) false
  p.bootExisting
  p.activate
  discard <| waitUntil 3000 (every := 10) do return (← p.app.controller.get).issue.isSome
  check "declined: one authentication prompt" ((← p.authAttempts.get) == 1)
  check "declined: not backed up, typed authenticationRequired issue"
    ((← p.backend.cloudStatus).statusTitle == "Not backed up" && (← p.backend.cloudStatus).issue == some .authenticationRequired)
  p.backend.cloudTick
  p.activate
  IO.sleep 100
  check "declined: not asked again in the same foreground session" ((← p.authAttempts.get) == 1 && !(← p.app.controller.get).enabled)
  p.backend.cloudScene false
  p.backend.stopNetworking
  -- testUnavailableCloudLeavesExistingWalletUsableWithoutAuthenticationPrompt
  let p ← cloudPhone root "unavailable" (← newKeys) false
  p.cloud.accountUnavailable.set true
  p.bootExisting
  p.activate
  discard <| waitUntil 3000 (every := 10) do return (← p.app.controller.get).issue.isSome
  let st ← p.backend.cloudStatus
  check "unavailable iCloud: no authentication prompt" ((← p.authAttempts.get) == 0)
  check "unavailable iCloud: signedOut issue, not backed up, still automatic"
    (st.issue == some .signedOut && st.statusTitle == "Not backed up" && st.automaticEnabled)
  let manual ← match ImportBundle.decode (← p.backend.exportBundle false) with
    | .ok b => pure b | .error _ => throw "the manual export does not decode"
  check "unavailable iCloud: the manual export still works, without the words" (manual.network == "signet" && manual.mnemonic.isNone)
  p.backend.cloudScene false
  p.backend.stopNetworking
  -- testModeChangesDoNotUndoExplicitBackupOptOut
  let p ← cloudPhone root "optout" (← newKeys) false
  p.bootExisting
  p.backend.setAutomaticCloudBackup false
  p.backend.updateSettings { p.settings with ownDisplayName := "Me" }
  p.backend.updateSettings p.settings
  p.activate
  IO.sleep 100
  check "opt-out: survives mode changes" (!(← p.backend.cloudStatus).automaticEnabled && (← p.authAttempts.get) == 0)
  p.backend.cloudScene false
  p.backend.stopNetworking
  -- testNewAndLegacyUnfinishedWalletsOpenWithoutPhraseChecklist (creation prepares the backup itself)
  let keys ← newKeys
  let p ← cloudPhone root "create" keys true
  p.cloud.failing.set true
  discard <| p.backend.openWallet .signet p.dir
  p.activate
  let id ← p.backend.createWallet .signet p.dir
  let st ← p.app.controller.get
  check "creation: the backup is prepared without an Enable action" st.enabled
  check "creation: local ciphertext is not an iCloud acknowledgement" st.lastSaved.isNone
  let flag := System.FilePath.mk p.dir / s!"backup-pending.{id}"
  IO.FS.writeFile flag ""
  p.backend.stopNetworking
  let rebooted ← cloudPhone root "create" keys true
  let r ← rebooted.backend.openWallet .signet p.dir
  check "a legacy unfinished checklist opens ready, its flag cleared" ((r matches .opened _) && !(← flag.pathExists))
  let model := (onHost (.created 0 id) ({ stage := .onboarding, active := true } : Model)).1
  check "creation lands on the wallet, with no checklist, only the Bluetooth card" (model.stage == .ready && model.walletID == some id && model.sheets == [.bluetoothIntro])

/-- Restore from iCloud end to end: phone A's backup (people included) restores on phone B, which then keeps
its own record bound to the same account. -/
def restoreFromICloud (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let sharedKeys ← Real.memoryCloudKeys
  let a ← cloudPhone root "restoreA" (← newKeys) true (some cloud) (some sharedKeys)
  discard <| a.backend.openWallet .signet a.dir
  a.activate
  let id ← a.backend.createWallet .signet a.dir
  let bob ← need "bob" (Wallet.create .signet (← newKeys) none (some (ByteArray.mk (Array.replicate 16 0xB0))))
  let card ← match ← (RecordsReal.ownPersonCard bob "Bob").run with
    | .ok c => pure c.serialized | .error _ => throw "card"
  discard <| a.backend.addPerson "Bob" (some card) none none none
  a.backend.updateSettings { a.settings with ownDisplayName := "Alice" }
  cloudOk <| a.app.controller.update do
    let bundle ← a.app.exportedBundle
    return { bundle, appState := some (← a.app.cloudAppState bundle).encoded }
  check "restore: phone A's backup is saved" ((← a.backend.cloudStatus).statusTitle == "Backed up") (reprStr (← a.backend.cloudStatus))
  a.backend.cloudScene false
  a.backend.stopNetworking
  let b ← cloudPhone root "restoreB" (← newKeys) true (some cloud) (some sharedKeys)
  discard <| b.backend.openWallet .signet b.dir
  b.backend.discoverCloudBackups
  let found := (← b.backend.cloudStatus).available
  check "restore: the new phone finds the backup" (found.length == 1)
  let some backup := found.head? | throw "no backup found"
  let .restored restoredID verified context ← b.backend.restoreCloudBackup .signet b.dir backup.id
    | throw "restore unexpectedly cancelled"
  check "restore: the same wallet" (restoredID == id)
  check "restore: one authentication" ((← b.authAttempts.get) == 1)
  check "restore: no peer yet, verification waits" verified.isNone
  -- the format keeps its Advanced switch (the Swift app reads it): this app's one mode writes it on
  check "restore: the display name comes back, and the format's Advanced switch with it" (context == some ("Alice", true))
  check "restore: saved people come back" ((← b.backend.records).people.any (·.name == "Bob"))
  let st ← b.app.controller.get
  check "restore: this phone keeps its own backup, bound to the account" (st.enabled && st.lastSaved.isNone &&
    (st.configuration.bind (·.account)) == some "first-account" && (st.configuration.map (·.backup.id)) != some backup.id)
  check "restore: a second restore is refused" (← fails (b.backend.restoreCloudBackup .signet b.dir backup.id))
  b.backend.stopNetworking

/-- A second wallet added from iCloud beside the one a phone already keeps. The restore list says which
wallet each backup is of and leaves out the phone's own; the restored wallet goes in a slot of its own with a
backup record of its own; the first wallet's file, its backup's record and its settings are not touched; a
wallet already kept is refused; and "automatic backup off" is each wallet's own. -/
def secondWalletFromICloud (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let sharedKeys ← Real.memoryCloudKeys
  -- another device, another wallet, backed up
  let a ← cloudPhone root "secondA" (← newKeys) true (some cloud) (some sharedKeys)
  let other ← need "the other wallet" (Wallet.create .signet a.keys (some (System.FilePath.mk a.dir / "wallet.json")) (some (ByteArray.mk (Array.replicate 16 0xA7))))
  discard <| a.backend.openWallet .signet a.dir
  a.activate
  unless ← waitUntil 5000 (every := 10) (do return (← a.app.controller.get).lastSaved.isSome) do throw "the other device's backup was not saved"
  a.backend.cloudScene false
  a.backend.stopNetworking
  -- this phone and its own wallet, backed up too. While its iCloud is listing, the app's tick may run (it runs
  -- every second): on 0.9.20 to 0.9.22 the tick pointed the backup at the empty place and so ended the search,
  -- and "Add a wallet" offered no restore at all
  let during ← IO.mkRef (pure () : IO Unit)
  let listing : Real.CloudBackupStore := { cloud.store with list := fun n => do (← during.get); cloud.store.list n }
  let b ← cloudPhone root "secondB" (← newKeys) true (some cloud) (some sharedKeys) (store := some listing)
  during.set do
    during.set (pure ())
    b.backend.cloudTick
  discard <| b.backend.openWallet .signet b.dir
  b.activate
  let own ← b.backend.createWallet .signet b.dir
  unless ← waitUntil 5000 (every := 10) (do return (← b.app.controller.get).lastSaved.isSome) do throw "this phone's backup was not saved"
  check "two wallets, two backups" (own != other.id && (← cloud.count) == 2)
  let ownBackup := ((← b.app.controller.get).configuration.map (·.backup.id)).getD ""
  let walletFile := System.FilePath.mk b.dir / "wallet.json"
  let configFile := System.FilePath.mk b.dir / "cloud-backup.json"
  let (walletBefore, configBefore) := (← IO.FS.readBinFile walletFile, ← IO.FS.readBinFile configFile)
  let recordBefore := ((← cloud.records.get).find? (·.id == ownBackup)).map (·.savedAt)
  -- a place for a wallet to be added: nothing is there yet
  let slot ← Real.freeSlot b.dir
  let added := Real.slotDir b.dir slot
  IO.FS.createDirAll added
  check "the place for a second wallet is empty" (slot == "1" && ((← b.backend.openWallet .signet added) matches .missing))
  during.set do
    during.set (pure ())
    b.backend.cloudTick
  b.backend.discoverCloudBackups
  let found := (← b.backend.cloudStatus).available
  check "the list offers the other wallet's backup, named, and not this phone's own"
    (found.map (·.walletID) == [some other.id]) (reprStr found)
  let some backup := found.head? | throw "no backup offered"
  let .restored restoredID _ _ ← b.backend.restoreCloudBackup .signet added backup.id
    | throw "second wallet restore unexpectedly cancelled"
  check "the other wallet is restored beside the first" (restoredID == other.id && (← Real.holdsWallet added))
  check "both are kept, the restored one open"
    ((← b.backend.wallets b.dir) == [{ id := own, slot := "", active := false }, { id := other.id, slot := "1", active := true }])
    (reprStr (← b.backend.wallets b.dir))
  check "the first wallet's file and its backup's record are as they were"
    ((← IO.FS.readBinFile walletFile) == walletBefore && (← IO.FS.readBinFile configFile) == configBefore &&
     ((← cloud.records.get).find? (·.id == ownBackup)).map (·.savedAt) == recordBefore)
  let st ← b.app.controller.get
  check "the restored wallet keeps a backup record of its own on this phone"
    (st.enabled && (st.configuration.map (·.backup.id)) != some backup.id && (st.configuration.map (·.backup.id)) != some ownBackup)
  -- the same wallet again, into another place
  let again := Real.slotDir b.dir (← Real.freeSlot b.dir)
  IO.FS.createDirAll again
  discard <| b.backend.openWallet .signet again
  b.backend.discoverCloudBackups
  check "a wallet already kept is no longer offered" ((← b.backend.cloudStatus).available.isEmpty)
    (reprStr (← b.backend.cloudStatus).available)
  check "…and is refused if asked for, with nothing written"
    ((← fails (b.backend.restoreCloudBackup .signet again backup.id)) && !(← Real.holdsWallet again))
  -- "automatic backup off" is a wallet's own
  -- (the app's tick points the backup at the wallet now open, as it does every second while the app is open)
  discard <| b.backend.openWallet .signet added
  b.backend.setAutomaticCloudBackup false
  check "off for the restored wallet" (!(← b.backend.cloudStatus).automaticEnabled)
  discard <| b.backend.openWallet .signet b.dir
  b.backend.cloudTick
  check "the first wallet's is still on, and its backup is still its own"
    ((← b.backend.cloudStatus).automaticEnabled && ((← b.app.controller.get).configuration.map (·.backup.id)) == some ownBackup)
  discard <| b.backend.openWallet .signet added
  b.backend.cloudTick
  check "…and the restored wallet's still off, after a switch away and back" (!(← b.backend.cloudStatus).automaticEnabled)
  b.backend.stopNetworking

/-! ## The screens: onboarding without a checklist, the home's backup line, Settings → Backup -/

def rendered (h : H) : String := (LeanNative.Html.toWire h).toJson.compress

def onboardingScreens : TM Unit := do
  let m : Model := { stage := .onboarding, active := true }
  let plain := rendered (view m)
  check "onboarding: no phrase checklist" (!contains plain "writtenDownToggle" && !contains plain "I have written the words down")
  check "onboarding: create and restore from a file" (contains plain "createWalletButton" && contains plain "importWalletButton" &&
    contains plain "Restore from a file")
  check "onboarding: softened backup footer without manual-backup nag"
    (contains plain "Recovery words and backup controls are in Settings → Backup." && !contains plain "No iCloud?")
  check "onboarding: transient offline issue stays quiet"
    (!contains (rendered (view { m with cloud := { issue := some .offline } })) CloudIssue.offline.message)
  check "onboarding: actionable issue still shows"
    (contains (rendered (view { m with cloud := { issue := some .signedOut } })) CloudIssue.signedOut.message)
  check "onboarding: iCloud said up front" (contains plain "automatically backs up your wallet with iCloud when available")
  check "onboarding: no iCloud restore without a backup" (!contains plain "restoreCloudBackupButton")
  check "onboarding: …and a way to look again" (contains plain Ids.checkCloudAgainButton && contains plain "Look for iCloud backups again")
  check "onboarding: on mainnet the network is folded behind Use a test network" (contains plain "onboardingTestNetwork" &&
    contains plain "Use a test network")
  let found := rendered (view { m with cloud := { available := [{ id := "A", savedAtText := "10/27/2026, 7:28 PM" }] } })
  check "onboarding: a saved backup offers the iCloud restore" (contains found "restoreCloudBackupButton" && contains found "1 saved backup(s) found.")
  let (m2, cs) := step (.cloud .openRestore) { m with cloud := { available := [{ id := "A", savedAtText := "10/27/2026, 7:28 PM" }] } }
  check "onboarding: the restore sheet looks again" (m2.hasSheet .cloudRestore && cs.any (· matches .discoverCloud))
  let sheet := rendered (view m2)
  check "restore sheet: lists the backup by date" (contains sheet "Choose a saved backup" && contains sheet "10/27/2026, 7:28 PM")
  let offlineSheet := rendered (view { m2 with cloud := { m2.cloud with issue := some .offline } })
  check "restore sheet: shows offline message when explicitly restoring" (contains offlineSheet CloudIssue.offline.message)
  let (m3, cs) := step (.cloud (.restore "A")) m2
  check "restore sheet: restoring" (m3.onboarding.restoring && cs.any (· matches .restoreCloud ..))
  let (m4, cs) := onHost (.cloudRestored m3.generation "W" none (some ("Alice", true))) m3
  check "restore sheet: restored, with the context's display name saved" (m4.onboarding.restored && m4.settings.ownDisplayName == "Alice" &&
    cs.any (· matches .saveSettings _))
  -- the backup's Advanced switch flips no mode: the settings are the same with it off
  let (m4off, _) := onHost (.cloudRestored m3.generation "W" none (some ("Alice", false))) m3
  check "restore sheet: the backup's Advanced switch changes nothing" ((Lean.toJson m4off.settings).compress == (Lean.toJson m4.settings).compress)
  check "restore sheet: says verification waits for peers"
    (contains (rendered (view m4)) "Restored. Network verification will resume when peers are reachable.")
  let (m5, _) := step .finishOnboarding m4
  check "restore sheet: Continue lands on the wallet, then the Bluetooth card" (m5.stage == .ready && m5.sheets == [.bluetoothIntro])
  let signet := rendered (view { m with settings := { network := .signet } })
  check "onboarding: a signet wallet keeps the network picker" (contains signet "onboardingNetworkPicker")
  -- the home's backup section across every state
  let home (c : CloudStatus) := rendered (.list (homeSections { stage := .ready, cloud := c, walletID := some "w" }) : H)
  let notYet := home {}
  check "home: not backed up links to iCloud backup settings, never manual backup file"
    (contains notYet "Not backed up" && contains notYet Ids.homeCloudBackupButton &&
     !contains notYet "Save a backup file" && !contains notYet "Until iCloud backup works")
  let signedOut := home { statusTitle := "Not backed up", issue := some .signedOut }
  check "home: signedOut shows plain copy and iCloud backup link, never manual backup or iCloud Drive"
    (contains signedOut CloudIssue.signedOut.message && contains signedOut Ids.homeCloudBackupButton &&
     !contains signedOut "Save a backup file" && !contains signedOut "iCloud Drive")
  let storageFull := home { statusTitle := "Not backed up", issue := some .storageFull }
  check "home: storageFull shows plain copy and iCloud backup link"
    (contains storageFull CloudIssue.storageFull.message && contains storageFull Ids.homeCloudBackupButton &&
     !contains storageFull "Save a backup file")
  let waitingOffline := home { statusTitle := "Waiting for connection", issue := some .offline }
  check "home: offline retry stays calm with no error text and no link"
    (contains waitingOffline "Waiting for connection" && !contains waitingOffline CloudIssue.offline.message &&
     !contains waitingOffline Ids.homeCloudBackupButton && !contains waitingOffline "Save a backup file")
  let backedUpOffline := home { statusTitle := "Backed up", lastSavedText := some "10/27/2026, 7:28 PM", enabled := true, issue := some .offline }
  check "home: backed up while offline stays Backed up with no error noise"
    (contains backedUpOffline "Backed up" && contains backedUpOffline "Last saved 10/27/2026, 7:28 PM" &&
     !contains backedUpOffline CloudIssue.offline.message && !contains backedUpOffline Ids.homeCloudBackupButton)
  let turnedOff := home { automaticEnabled := false, statusTitle := "Off" }
  check "home: off shows Off + iCloud backup link with zero scare text"
    (contains turnedOff "\"Off\"" && contains turnedOff Ids.homeCloudBackupButton &&
     !contains turnedOff "Save a backup file" && !contains turnedOff "Until iCloud")
  let noEntitlement := home { statusTitle := "Not available", issue := some .unavailableInBuild }
  check "home: build without entitlement says Not available + plain explanation, no button"
    (contains noEntitlement "Not available" && contains noEntitlement CloudIssue.unavailableInBuild.message &&
     !contains noEntitlement Ids.homeCloudBackupButton && !contains noEntitlement "Sign in to" && !contains noEntitlement "Save a backup file")
  let done := home { statusTitle := "Backed up", lastSavedText := some "10/27/2026, 7:28 PM", enabled := true }
  check "home: backed up, with its date, and no link"
    (contains done "Last saved 10/27/2026, 7:28 PM" && !contains done Ids.homeCloudBackupButton && !contains done "Save a backup file")
  -- Every CloudIssue message stays free of legacy/misleading copy
  let allIssues : List CloudIssue :=
    [.signedOut, .keychainUnavailable, .offline, .storageFull, .accountChanged,
     .unreadableBackup, .unsupportedWallet, .unavailableInBuild, .settingsUnreadable,
     .authenticationRequired, .backupFailed]
  for issue in allIssues do
    let msg := issue.message
    check s!"CloudIssue.{reprStr issue}: plain copy without iCloud Drive, backup file, or WalletCore"
      (!msg.isEmpty && !contains msg "iCloud Drive" && !contains msg "backup file" &&
       !contains msg "WalletCore" && !contains msg "Backup needs attention")
  -- Plain error messages for silent payment codes and WalletFailure.named (no legacy Swift NSError strings)
  check "silentPaymentErrorText: wrongHRP is plain"
    (Real.silentPaymentErrorText (.wrongHRP "sp" "tsp") == "That silent payment code belongs to a different Bitcoin network.")
  check "silentPaymentErrorText: invalidEncoding is plain"
    (!contains (Real.silentPaymentErrorText .invalidEncoding) "WalletCore")
  check "namedText: fallback never leaks WalletCore"
    (!contains (Real.namedText "someInternalCase") "WalletCore")
  -- Settings → Backup: always the iCloud backup, the file and the recovery words
  let advanced : Model := { walletID := some "w" }
  let advBackup := rendered (backupSection advanced)
  check "Settings → Backup: iCloud backup, the file and the recovery phrase" (contains advBackup "iCloud backup" &&
    contains advBackup "exportBundleButton" && contains advBackup "revealPhraseButton")
  check "Settings: the plain footer and button" (contains advBackup "iCloud backup keeps this wallet automatically. A backup file is a copy you keep yourself." &&
    contains advBackup "Save a backup file" && !contains advBackup "Back up wallet")
  let row (c : CloudStatus) := rendered (backupSection { advanced with cloud := c })
  check "Settings row: backed up, how long ago" (contains (row { statusTitle := "Backed up", lastSavedAgo := some "5 min" }) "Backed up 5 min ago")
  check "Settings row: not available in this build" (contains (row { statusTitle := "Not available", issue := some .unavailableInBuild }) "Not available")
  check "Settings row: off" (contains (row { automaticEnabled := false, statusTitle := "Off" }) "\"Off\"")
  check "Settings row: waiting for connection" (contains (row { statusTitle := "Waiting for connection", issue := some .offline }) "Waiting for connection")
  let (sheetModel, _) := step (.backup .openExport) advanced
  let exportText := rendered (exportSheet sheetModel [])
  check "Backup file sheet: its title and what it does" (contains exportText "Backup file" && !contains exportText "Back up wallet" &&
    contains exportText "Saves a file you can keep in Files or send to yourself. Restore it from Restore from a file." &&
    contains exportText "Without the recovery phrase the file restores your history but not the ability to spend.")
  let (asking, _) := step (.backup .createExport) { sheetModel with exportState := { includeMnemonic := true } }
  check "Backup file sheet: the phrase still asks first" (asking.confirm == some .exportWithPhrase)
  let (m6, _) := step (.cloud .openBackup) advanced
  let controls := rendered (cloudBackupSheet m6 [])
  check "iCloud backup: the automatic switch, no manual backup nag"
    (contains controls "automaticCloudBackupToggle" && contains controls "Automatic iCloud backup" &&
     !contains controls "Keep a backup file too.")
  let offlineControls := rendered (cloudBackupSheet { m6 with cloud := { statusTitle := "Waiting for connection", issue := some .offline } } [])
  check "iCloud backup sheet: shows offline note when opened" (contains offlineControls CloudIssue.offline.message)
  check "iCloud backup: the switch asks the backend" ((step (.cloud (.setAutomatic false)) m6).2.any (· matches .setAutomaticCloud false))

/-- The shell's CloudKit answers classified into typed `CloudError` / `CloudIssue`, never leaking raw
CloudKit details to the UI. -/
def shellAnswers : TM Unit := do
  let answering (answer : Lean.Json) : Real.Ask := fun _ _ => pure (Task.pure answer)
  let accountErr (answer : Lean.Json) : IO (Except Real.CloudError String) :=
    (Real.shellCloudStore (answering answer)).account.run
  check "missingEntitlement -> unavailableInBuild"
    (exceptEq (← accountErr (Lean.Json.mkObj [("error", Lean.Json.str "missingEntitlement"), ("detail", Lean.Json.str "raw internal detail")])) (.error (.issue .unavailableInBuild)))
  check "notAuthenticated -> signedOut"
    (exceptEq (← accountErr (Lean.Json.mkObj [("error", Lean.Json.str "notAuthenticated")])) (.error (.issue .signedOut)))
  check "permissionFailure -> signedOut"
    (exceptEq (← accountErr (Lean.Json.mkObj [("error", Lean.Json.str "permissionFailure")])) (.error (.issue .signedOut)))
  check "noAccount -> signedOut"
    (exceptEq (← accountErr (Lean.Json.mkObj [("status", Lean.Json.str "noAccount"), ("user", Lean.Json.null)])) (.error (.issue .signedOut)))
  check "temporarilyUnavailable -> offline"
    (exceptEq (← accountErr (Lean.Json.mkObj [("status", Lean.Json.str "temporarilyUnavailable"), ("user", Lean.Json.null)])) (.error (.issue .offline)))
  check "networkUnavailable -> offline (never leaks raw detail)"
    (exceptEq (← accountErr (Lean.Json.mkObj [("error", Lean.Json.str "networkUnavailable"), ("detail", Lean.Json.str "CKErrorDomain 3")])) (.error (.issue .offline)))
  let classified (name : String) : IO (Except Real.CloudError String) :=
    accountErr (Lean.Json.mkObj [("error", Lean.Json.str name), ("detail", Lean.Json.str "raw internal detail")])
  for name in Real.cloudTransientErrors do
    check s!"{name} -> offline (waiting cures it)" (exceptEq (← classified name) (.error (.issue .offline)))
  -- what waiting does not cure is never "offline", which Home shows as nothing to do
  for name in ["limitExceeded", "serverRejectedRequest", "zoneNotFound", "userDeletedZone", "invalidArguments",
               "incompatibleVersion", "internalError", "notFound", "badArgs", "unknown"] do
    check s!"{name} -> backupFailed, not offline" (exceptEq (← classified name) (.error (.issue .backupFailed)))
  check "backupFailed is not transient: the screens say Not backed up and show its note"
    (!CloudIssue.backupFailed.isTransient && CloudIssue.offline.isTransient)
  check "quotaExceeded -> storageFull (never leaks raw detail)"
    (exceptEq (← accountErr (Lean.Json.mkObj [("error", Lean.Json.str "quotaExceeded"), ("detail", Lean.Json.str "CKErrorDomain 25")])) (.error (.issue .storageFull)))
  check "operationCancelled -> cancelled"
    (exceptEq (← accountErr (Lean.Json.mkObj [("error", Lean.Json.str "operationCancelled")])) (.error .cancelled))
  check "available: the user"
    (exceptEq (← accountErr (Lean.Json.mkObj [("status", Lean.Json.str "available"), ("user", Lean.Json.str "_u")])) (.ok "_u"))

/-- A Keychain as the shell's `keychain.*` capabilities give it: items by key, each with whether it is behind
the person's presence, which a read that names no kept authentication is refused as a device refuses it. -/
def fakeKeychain : IO (Real.Ask × IO.Ref (Std.HashMap String (String × Bool))) := do
  let items ← IO.mkRef ({} : Std.HashMap String (String × Bool))
  let ask : Real.Ask := fun name args => do
    let obj := Lean.Json.mkObj
    let key := (args.getObjValAs? String "key").toOption.getD ""
    let answer ← match name with
      | "keychain.add" =>
        -- the item as the device keeps it: the bytes given as hex (or text), read back as text
        let value := match (args.getObjValAs? String "hex").toOption with
          | some h => ((ofHex? h).bind String.fromUTF8?).getD ""
          | none => (args.getObjValAs? String "value").toOption.getD ""
        let guarded := (args.getObjValAs? String "access").toOption == some "userPresence"
        if (← items.get).contains key then pure (obj [("ok", false), ("status", (-25299 : Int)), ("exists", true)])
        else
          items.modify (·.insert key (value, guarded))
          pure (obj [("ok", true), ("status", (0 : Int)), ("exists", false), ("access", if guarded then "userPresence" else "unlocked")])
      | "keychain.get" =>
        let named := (args.getObjValAs? String "context").toOption.isSome
        match (← items.get)[key]? with
        | none => pure (obj [("value", Lean.Json.null), ("status", (-25300 : Int))])
        | some (v, guarded) =>
          if guarded && !named then pure (obj [("value", Lean.Json.null), ("status", (-25308 : Int))])
          else pure (obj [("value", Lean.Json.str v), ("status", (0 : Int))])
      | "keychain.delete" =>
        items.modify (·.erase key)
        pure (obj [("ok", true), ("status", (0 : Int))])
      | _ => pure Lean.Json.null
    pure (Task.pure answer)
  return (ask, items)

/-- 0.9.17 to 0.9.21 put every item the app added behind the person's presence, the sealed stores' keys
included: a store first sealed then read as damaged at the next launch, with nobody there to give the key.
Now only the wallet's secret goes behind it, and a key an earlier build put there is moved out the next time
the person authenticates, keeping its bytes, so the files it sealed read again. A move cut short is finished
from where the key waited. -/
def storeKeysOutOfPresence (root : System.FilePath) : TM Unit := do
  let (ask, items) ← fakeKeychain
  let ks := Real.shellKeyStore ask Real.walletService true
  let vault := StoreKeyVault.ofKeyStore ks
  let net : BitcoinNetwork := .signet
  let account := ({ store := SignerStore.storeName, keys := vault } : StoreSeal).account net
  let main := accountPrefix ++ account
  Real.keychainContext.set none
  refusedStoreKeys.set #[]
  -- what an earlier build left: the signers' key behind the person's presence, and the file it sealed
  let key ← IO.getRandomBytes 32
  let text := String.fromUTF8! (WalletSecret.masterKey (hex key)).serialized
  items.modify (·.insert main (text, true))
  let dir := root / "lockedKeys"
  IO.FS.createDirAll dir
  let path := dir / SignerStore.fileName
  IO.FS.writeBinFile path (SealedStoreFile.sealed (SignerStore.encode #[]) SignerStore.storeName net key)
  let (opened, _) ← SignerStore.configure vault (some path) net
  check "an earlier build's key: the store reads as damaged with nobody there" opened.isDamaged
  check "…and the key is noted as refused, not lost" ((← refusedStoreKeys.get) == #[account])
  check "…and the file is untouched" ((← IO.FS.readBinFile path).size > 0)
  -- the wallet's secret and a new store's key, as this build adds them
  discard (ks.store (.mnemonic "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about") "w1").run
  let other := accountPrefix ++ ({ store := "people", keys := vault } : StoreSeal).account net
  discard <| (vault.establishKey (({ store := "people", keys := vault } : StoreSeal).account net)).run
  check "the wallet's secret goes behind the person's presence" (((← items.get)["w1"]?).map (·.2) == some true)
  check "a new store's key does not" (((← items.get)[other]?).map (·.2) == some false)
  -- nobody has authenticated: nothing moves
  check "with nobody there, nothing is moved" ((← repairRefusedStoreKeys ks).isEmpty && ((← items.get)[main]?).map (·.2) == some true)
  -- the person authenticates (any action that asks): the key comes out from behind it, with its bytes
  Real.keychainContext.set (some "ctx")
  let moved ← repairRefusedStoreKeys ks
  Real.keychainContext.set none
  check "authenticated: the refused key is moved out from behind the person's presence" (moved == [account])
  check "…as the same key, and no copy is left waiting"
    (((← items.get)[main]?) == some (text, false) && !(← items.get).contains (main ++ movingSuffix))
  check "…and none is still refused" ((← refusedStoreKeys.get).isEmpty)
  let (again, _) ← SignerStore.configure vault (some path) net
  check "the store it sealed reads again, with nobody there" (!again.isDamaged)
  -- a move cut short after the item went and before it came back: the key waits under its copy
  items.modify fun m => (m.erase main).insert (main ++ movingSuffix) (text, false)
  check "a move cut short: the key is taken from where it waited" (((← (vault.key account).run).toOption.join) == some key)
  check "…put back as it should be, and the copy gone"
    (((← items.get)[main]?) == some (text, false) && !(← items.get).contains (main ++ movingSuffix))

/-- The shell adapters over LeanNative's typed clients, against a scripted shell: what they ask and how
they read the answers into this app's errors and texts. -/
def shellAdapters : TM Unit := do
  let asked ← IO.mkRef (#[] : Array (String × Lean.Json))
  let script ← IO.mkRef (fun (_ : String) (_ : Lean.Json) => Lean.Json.null)
  let ask : Real.Ask := fun name args => do
    asked.modify (·.push (name, args))
    pure (Task.pure ((← script.get) name args))
  let answer (f : String → Lean.Json → Lean.Json) : IO Unit := do asked.set #[]; script.set f
  let obj := Lean.Json.mkObj
  let store := Real.shellKeyStore ask
  let secret := Winnow.Keys.WalletSecret.mnemonic "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about"
  -- store: one atomic keychain.add, never a read first
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("exists", false)]
  let stored ← (store.store secret "w1").run
  check "store: one keychain.add, nothing read first" (stored matches .ok () && ((← asked.get).map (·.1)) == #["keychain.add"])
  answer fun _ _ => obj [("ok", false), ("status", (-25299 : Int)), ("exists", true)]
  check "store: an occupied id is alreadyExists" ((← (store.store secret "w1").run) matches .error (.alreadyExists "w1"))
  -- load: the secret; a missing or raw-bytes item is notFound; a locked device is its status, not "no wallet"
  answer fun _ _ => obj [("value", Lean.Json.str (String.fromUTF8! secret.serialized)), ("status", (0 : Int))]
  check "load: the secret" ((← (store.load "w1").run) matches .ok _)
  answer fun _ _ => obj [("value", Lean.Json.null), ("status", (-25300 : Int))]
  check "load: missing is notFound" ((← (store.load "w1").run) matches .error (.notFound "w1"))
  answer fun _ _ => obj [("value", Lean.Json.null), ("status", (0 : Int))]
  check "load: raw bytes are notFound" ((← (store.load "w1").run) matches .error (.notFound "w1"))
  answer fun _ _ => obj [("value", Lean.Json.null), ("status", (-25308 : Int))]
  check "load: a locked device is errSecInteractionNotAllowed" ((← (store.load "w1").run) matches .error (.keychain (-25308)))
  answer fun _ _ => obj [("hex", Lean.Json.null), ("status", (-25300 : Int))]
  check "loadBytes: missing is none" ((← (store.loadBytes "w1").run) matches .ok none)
  -- as it was: nothing of an access control or a kept authentication is sent by a store that was not asked for it
  let sent (name : String) : IO (Array Lean.Json) := do return (← asked.get).filterMap fun (n, a) => if n == name then some a else none
  let has (a : Lean.Json) (key : String) : Bool := (a.getObjVal? key).toOption.isSome
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("exists", false)]
  discard (store.store secret "w1").run
  check "store: without userPresence, no access is sent" ((← sent "keychain.add").all (!has · "access"))
  check "upgradeProtection: without userPresence, nothing is asked"
    ((← (store.upgradeProtection "w1").run) matches .ok false && (← sent "keychain.protect").isEmpty)
  -- the wallet's secret behind the person's presence (SEC-060): the secret's item alone, and its reads under
  -- the authentication the app keeps
  let guarded := Real.shellKeyStore ask Real.walletService true
  Real.keychainContext.set none
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("exists", false), ("access", "userPresence")]
  let stored ← (guarded.store secret "w1").run
  check "userPresence: the secret is added behind the person's presence, by one keychain.add"
    (stored matches .ok () && ((← asked.get).map (·.1)) == #["keychain.add"] &&
     ((← sent "keychain.add").map fun a => (a.getObjValAs? String "access").toOption) == #[some "userPresence"])
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("exists", false)]
  discard (guarded.storeBytes (ByteArray.mk #[1, 2, 3]) "store-key.people.main").run
  check "userPresence: an item kept as bytes is not: a sync pass reads it with nobody there"
    ((← sent "keychain.add").size == 1 && (← sent "keychain.add").all (!has · "access"))
  -- a sealed store's key goes through `store`, as text, and is read at every launch with nobody there
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("exists", false)]
  discard (guarded.store (.masterKey (String.ofList (List.replicate 64 'a'))) "store-key.signers.main").run
  check "userPresence: a store's key, kept as text, is not behind the person's presence"
    ((← sent "keychain.add").size == 1 && (← sent "keychain.add").all (!has · "access"))
  answer fun _ _ => obj [("value", Lean.Json.null), ("status", (-25308 : Int))]
  check "userPresence: a read with no authentication names none, and the Keychain's refusal is its status"
    ((← (guarded.load "w1").run) matches .error (.keychain (-25308)) && (← sent "keychain.get").all (!has · "context"))
  answer fun name _ =>
    if name == "keychain.get" then obj [("value", Lean.Json.str (String.fromUTF8! secret.serialized)), ("status", (0 : Int))]
    else obj [("ok", true)]
  let twoReads : IO Bool := do
    let first ← (guarded.load "w1").run
    let second ← (guarded.load "w1").run
    return first matches .ok _ && second matches .ok _
  let read ← (Real.withKeychainContext ask (some "kept-1") twoReads : IO Bool)
  check "userPresence: under a kept authentication every read names it, and it is ended once, after"
    (read && ((← sent "keychain.get").map fun a => (a.getObjValAs? String "context").toOption) == #[some "kept-1", some "kept-1"] &&
     ((← sent "auth.end").map fun a => (a.getObjValAs? String "context").toOption) == #[some "kept-1"] &&
     ((← asked.get).map (·.1)) == #["keychain.get", "keychain.get", "auth.end"] && (← Real.keychainContext.get).isNone)
  answer fun _ _ => obj [("ok", true)]
  let threw ← (Real.withKeychainContext ask (some "kept-2") (throw (IO.userError "the action failed") : IO Unit)).toBaseIO
  check "userPresence: an action that fails still ends its authentication"
    (threw matches .error _ && ((← sent "auth.end").map fun a => (a.getObjValAs? String "context").toOption) == #[some "kept-2"] &&
     (← Real.keychainContext.get).isNone)
  answer fun _ _ => obj [("value", Lean.Json.null), ("status", (-25308 : Int))]
  discard (guarded.load "w1").run
  check "userPresence: after it, a read names no authentication again" ((← sent "keychain.get").all (!has · "context"))
  -- an item an earlier build stored: one keychain.protect, in place; a wallet that only watches has none
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("changed", true), ("access", "userPresence")]
  check "upgradeProtection: one keychain.protect and nothing else, and it says it changed the item"
    ((← (guarded.upgradeProtection "w1").run) matches .ok true && ((← asked.get).map (·.1)) == #["keychain.protect"])
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int)), ("changed", false), ("access", "userPresence")]
  check "upgradeProtection: an item already protected is left" ((← (guarded.upgradeProtection "w1").run) matches .ok false)
  answer fun _ _ => obj [("ok", false), ("status", (-25300 : Int)), ("changed", false)]
  check "upgradeProtection: no item (a wallet that only watches) is not a failure" ((← (guarded.upgradeProtection "w1").run) matches .ok false)
  answer fun _ _ => obj [("ok", false), ("status", (-25293 : Int)), ("changed", false)]
  check "upgradeProtection: a refusal is its status" ((← (guarded.upgradeProtection "w1").run) matches .error (.keychain (-25293)))
  -- fetch: a response is a response; the shell's errors as the routed client's
  let fetch (reply : Lean.Json) : IO (Except Winnow.IO.NetError Winnow.IO.HttpHop) := do
    answer fun _ _ => reply
    (Real.shellFetch ask { url := "https://example.com/x", maximumBytes := 10 }).attempt
  check "fetch: a 404 is a response" ((← fetch (obj [("status", (404 : Nat)), ("body", "6869")])) matches .ok (.response 404 none _))
  check "fetch: tooLarge" ((← fetch (obj [("error", "tooLarge")])) matches .error (.http .tooLarge))
  check "fetch: bad-proxy is unavailable" ((← fetch (obj [("error", "bad-proxy")])) matches .error (.http .unavailable))
  check "fetch: a system error keeps its text" (match ← fetch (obj [("error", "offline"), ("code", (-1009 : Int)), ("domain", "NSURLErrorDomain")]) with
    | .error (.http (.transport t)) => t == "offline" | _ => false)
  check "fetch: a malformed answer is a bad response" ((← fetch (obj [("status", (200 : Nat))])) matches .error (.http .response))
  -- CloudKit: the account, then this app's record type, fields and container
  let cloud := Real.shellCloudStore ask
  let record (name network : String) (savedAt : Float) := obj [("name", Lean.Json.str name), ("type", "WalletBackup"),
    ("fields", obj [("network", Lean.Json.str network), ("savedAt", obj [("date", Lean.toJson savedAt)])])]
  let a := "6F9619FF-8B86-D011-B42D-00C04FC964FF"
  let b := "7F9619FF-8B86-D011-B42D-00C04FC964FF"
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("records", Lean.Json.arr #[record a "signet" 978_307_300, record b "signet" 978_307_400,
                                            record "not-a-uuid" "signet" 1, record a "mainnet" 2]), ("more", false)]
  let listed ← (cloud.list "signet").run
  check "list: this network's backups, newest first" (match listed with
    | .ok l => l.map (·.id) == #[b, a] && l.map (·.savedAt) == #[200, 100] | _ => false)
  check "list: the query names the record type, network and container" ((← asked.get).any fun (n, args) =>
    n == "cloudkit.query" && (args.getObjValAs? String "type").toOption == some "WalletBackup" &&
    (args.getObjValAs? String "container").toOption == some Real.cloudContainer && (args.getObjVal? "equals").toOption == some (obj [("network", "signet")]))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("error", "tooLarge")]
  check "load: an asset over the limit is unreadableBackup" (← cloudFailsWith (cloud.load a "_u") (.issue .unreadableBackup))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("error", "quotaExceeded"), ("code", (25 : Int)), ("detail", "iCloud storage is full")]
  check "load: quotaExceeded classifies as storageFull (no raw detail leak)" (← cloudFailsWith (cloud.load a "_u") (.issue .storageFull))
  -- the wrapping keys: synchronizable, 32 bytes
  let keys := Real.shellCloudKeys ask
  answer fun _ _ => obj [("hex", Lean.Json.null), ("status", (-25300 : Int))]
  check "keys: missing is keychainUnavailable" (← cloudFailsWith (keys.load a) (.issue .keychainUnavailable))
  check "keys: asked as a synchronizable item of this app's service" ((← asked.get).any fun (n, args) =>
    n == "keychain.get" && (args.getObjValAs? Bool "synchronizable").toOption == some true && (args.getObjValAs? String "service").toOption == some Real.cloudBackupKeyService)
  answer fun _ _ => obj [("hex", "0011"), ("status", (0 : Int))]
  check "keys: a key of the wrong size is unreadableBackup" (← cloudFailsWith (keys.load a) (.issue .unreadableBackup))
  answer fun _ _ => obj [("hex", "zzzz"), ("status", (0 : Int))]
  check "keys: malformed hex is unreadableBackup" (← cloudFailsWith (keys.load a) (.issue .unreadableBackup))
  answer fun _ _ => obj [("hex", Lean.Json.str (Winnow.hex (ByteArray.mk (Array.replicate 32 0x55)))), ("status", (0 : Int))]
  check "keys: 32-byte hex returns the key" ((← (keys.load a).run) matches .ok _)
  answer fun _ _ => obj [("ok", true), ("status", (0 : Int))]
  check "keys: create writes a 32-byte key" ((← (keys.create a).run) matches .ok _)
  answer fun _ _ => obj [("ok", false), ("status", (-25299 : Int))]
  check "keys: create failure is keychainUnavailable" (← cloudFailsWith (keys.create a) (.issue .keychainUnavailable))
  -- shellCloudStore: account statuses, list error, save (ok, accountChanged before/after, error), load (ok, missing asset, bad payload, id mismatch, accountChanged)
  answer fun _ _ => obj [("status", "noAccount")]
  check "account: noAccount is signedOut" (← cloudFailsWith cloud.account (.issue .signedOut))
  answer fun _ _ => obj [("status", "restricted")]
  check "account: restricted is signedOut" (← cloudFailsWith cloud.account (.issue .signedOut))
  answer fun _ _ => obj [("status", "temporarilyUnavailable")]
  check "account: temporarilyUnavailable is offline" (← cloudFailsWith cloud.account (.issue .offline))
  answer fun _ _ => obj [("error", "missingEntitlement")]
  check "account: missingEntitlement is unavailableInBuild" (← cloudFailsWith cloud.account (.issue .unavailableInBuild))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("error", "networkUnavailable")]
  check "list: query networkUnavailable is offline" (← cloudFailsWith (cloud.list "signet") (.issue .offline))
  let sampleBundle ← walletBundle .signet 7
  let sampleKey ← randomKey
  let sampleBackup ← need "shellCloudStore sample" (CloudWalletBackup.create sampleBundle sampleKey)
  let sampleBytes ← need "shellCloudStore encode" sampleBackup.encoded
  let sampleHex := Winnow.hex sampleBytes
  -- save: happy path, account changed before, account changed after, CloudKit save error
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("ok", true), ("record", record sampleBackup.id "signet" 978_307_300)]
  check "save: writes record and payload asset"
    ((← (cloud.save sampleBackup "_u").run) matches .ok () &&
     (← asked.get).any fun (n, args) => n == "cloudkit.save" &&
       (args.getObjValAs? String "name").toOption == some sampleBackup.id &&
       (args.getObjValAs? String "assetField").toOption == some "payload")
  check "save: different account before write is accountChanged"
    (← cloudFailsWith (cloud.save sampleBackup "_other") (.issue .accountChanged))
  let acctCalls ← IO.mkRef 0
  let switchingAsk : Real.Ask := fun name _ => do
    if name == "cloudkit.account" then
      let n ← acctCalls.modifyGet fun k => (k, k + 1)
      return Task.pure (obj [("status", "available"), ("user", if n == 0 then "_u" else "_other")])
    return Task.pure (obj [("ok", true), ("record", record sampleBackup.id "signet" 978_307_300)])
  check "save: account changing during write is accountChanged"
    (← cloudFailsWith ((Real.shellCloudStore switchingAsk).save sampleBackup "_u") (.issue .accountChanged))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("error", "quotaExceeded")]
  check "save: quotaExceeded is storageFull" (← cloudFailsWith (cloud.save sampleBackup "_u") (.issue .storageFull))
  -- load: happy path, missing asset, undecodable asset, id mismatch, account mismatch
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("record", record sampleBackup.id "signet" 978_307_300), ("asset", Lean.Json.str sampleHex)]
  check "load: decodes matching backup asset"
    (match ← (cloud.load sampleBackup.id "_u").run with | .ok bk => bk.id == sampleBackup.id | _ => false)
  check "load: wrong expected account before load is accountChanged"
    (← cloudFailsWith (cloud.load sampleBackup.id "_other") (.issue .accountChanged))
  check "load: mismatched record id in payload is accountChanged"
    (← cloudFailsWith (cloud.load a "_u") (.issue .accountChanged))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("record", record sampleBackup.id "signet" 978_307_300), ("asset", Lean.Json.null)]
  check "load: missing asset is unreadableBackup"
    (← cloudFailsWith (cloud.load sampleBackup.id "_u") (.issue .unreadableBackup))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("record", record sampleBackup.id "signet" 978_307_300), ("asset", "deadbeef")]
  check "load: corrupt backup bytes is unreadableBackup"
    (← cloudFailsWith (cloud.load sampleBackup.id "_u") (.issue .unreadableBackup))

/-- The existing wallet's preparation runs in LeanNative's EffectScope: the background or a wallet change
while the person answers the prompt ends it before the protected part (the words, the copy) starts, and
says nothing to the person. The prompt is held open by a gate, released after the change. -/
def scopedPreparationTests (root : System.FilePath) : TM Unit := do
  for (name, change) in [("background", fun (p : CloudPhone) => p.backend.cloudScene false),
                         ("wallet change", fun (p : CloudPhone) => p.app.walletChanged)] do
    let prompted ← IO.Promise.new
    let answer ← IO.Promise.new
    let loads ← IO.mkRef 0
    let base ← newKeys
    let keys : KeyStore IO := { base with load := fun id => do (loads.modify (· + 1) : IO Unit); base.load id }
    let p ← cloudPhone root s!"scoped-{name.replace " " "-"}" keys true
      (whileAuthenticating := do prompted.resolve (); discard <| IO.wait answer.result?)
    p.bootExisting
    p.activate
    let asked ← waitUntil 5000 (every := 10) prompted.isResolved
    let before ← loads.get
    change p
    answer.resolve ()
    -- the preparation's task ends (its scope's check after the answer); then nothing it would have done has happened
    let ended ← match ← p.app.preparationTask.get with
      | some t => do discard <| IO.wait t; pure true
      | none => pure false
    check s!"{name} during the prompt: the prompt was asked" asked
    check s!"{name} during the prompt: the preparation ends" ended
    check s!"{name} during the prompt: the words are not read" ((← loads.get) == before)
    check s!"{name} during the prompt: nothing is uploaded" ((← p.cloud.records.get).isEmpty)
    check s!"{name} during the prompt: no failure is shown" ((← p.app.controller.get).issue.isNone)
    p.backend.cloudScene false
    p.backend.stopNetworking

/-! ## The device check before the iCloud backup (#68) -/

/-- #68: the app's own device check (`WinnowApp.authenticateNow`, the one `chooseBackend` gives the backend)
before the iCloud backup's preparation and restore, over a shell whose `auth` answers as the person did
(LeanNative's `auth`: `ok`, and the system's text and `LAError` when not). Declined, the backup is not
prepared and the restore stops before the phone has a wallet; the restore, approved, goes
ahead. Test mode skips the check unless `WINNOW_E2E_DEVICE_AUTH=1`. -/
def declinedDeviceCheck (root : System.FilePath) : TM Unit := do
  let asked ← IO.mkRef (#[] : Array (String × Lean.Json))
  let declined := Lean.Json.mkObj [("ok", false), ("error", "Canceled by user."), ("name", "userCancel"), ("code", (-2 : Int))]
  let answer ← IO.mkRef declined
  let posted ← IO.mkRef (#[] : Array Host)
  let fx : LeanNative.Native.Effects Host :=
    { post := fun h => posted.modify (·.push h), cap := fun _ _ _ => pure (),
      ask := fun name args => do
        asked.modify (·.push (name, args))
        let auth ← answer.get
        return Task.pure (if name == "auth" then auth else Lean.Json.mkObj [("ok", true)]) }
  let prompts : IO (Array String) := do
    return (← asked.get).filterMap fun (n, a) => if n == "auth" then (a.getObjValAs? String "reason").toOption else none
  WinnowApp.e2eRef.set none
  -- an existing wallet's automatic preparation, declined
  let p ← cloudPhone root "check-prepare" (← newKeys) true (deviceCheck := some (WinnowApp.authenticateNow fx))
  p.bootExisting
  p.activate
  discard <| waitUntil 3000 (every := 10) do return (← p.app.controller.get).issue.isSome
  let st ← p.backend.cloudStatus
  let c ← p.app.controller.get
  check "declined check: the person is asked once, for the backup" ((← prompts) == #["Protect your wallet with automatic iCloud backup"])
  check "declined check: the backup is not prepared" (!c.enabled && c.configuration.isNone && st.statusTitle == "Not backed up")
  check "declined check: nothing is uploaded" ((← p.cloud.records.get).isEmpty && (← p.cloud.saveAttempts.get) == 0)
  check "declined check: typed authenticationRequired issue is recorded" (st.issue == some .authenticationRequired) (reprStr st.issue)
  p.backend.cloudTick
  IO.sleep 100
  check "declined check: not asked again in this foreground session" ((← prompts).size == 1 && !(← p.app.controller.get).enabled)
  p.backend.cloudScene false
  p.backend.stopNetworking
  -- phone A's backup, to restore on phone B
  let cloud ← Real.MemoryCloud.new
  let sharedKeys ← Real.memoryCloudKeys
  let a ← cloudPhone root "check-restoreA" (← newKeys) true (some cloud) (some sharedKeys)
  discard <| a.backend.openWallet .signet a.dir
  a.activate
  let id ← a.backend.createWallet .signet a.dir
  cloudOk <| a.app.controller.update do
    let bundle ← a.app.exportedBundle
    return { bundle, appState := some (← a.app.cloudAppState bundle).encoded }
  a.backend.cloudScene false
  a.backend.stopNetworking
  asked.set #[]
  let b ← cloudPhone root "check-restoreB" (← newKeys) true (some cloud) (some sharedKeys)
    (deviceCheck := some (WinnowApp.authenticateNow fx))
  discard <| b.backend.openWallet .signet b.dir
  b.backend.discoverCloudBackups
  let some backup := (← b.backend.cloudStatus).available.head? | throw "phone B finds no backup"
  -- the restore sheet's Restore, through the app's `perform` on phone B's backend
  WinnowApp.backendRef.set b.backend
  WinnowApp.rootDir.set (root / "check-restoreB").toString
  let found ← b.backend.cloudStatus
  let onboarding : Model := { stage := .onboarding, active := true, settings := { network := .signet }, cloud := found }
  let sheet := (step (.cloud .openRestore) onboarding).1
  let restore (m : Model) : TM Model := do
    let before := (← posted.get).size
    let (m, cs) := step (.cloud (.restore backup.id)) m
    for c in cs do WinnowApp.perform c fx
    unless ← waitUntil 10_000 (every := 5) (do return (← posted.get).size > before) do throw "the restore posted no answer"
    return (onHost (← posted.get)[before]! m).1
  let m ← restore sheet
  check "declined restore: the person is asked once" ((← prompts) == #["Restore your wallet and signing key from iCloud"])
  check "declined restore: the sheet says why and is no longer restoring"
    (m.onboarding.restoreError == some "Canceled by user." && !m.onboarding.restoring && !m.onboarding.restored && m.walletID.isNone)
    (reprStr m.onboarding.restoreError)
  check "declined restore: no wallet on the phone" (!(← (System.FilePath.mk b.dir / "wallet.json").pathExists) &&
    (← b.env.get).wallet.isNone && (← b.backend.openWallet .signet b.dir) matches .missing)
    (reprStr (← b.backend.openWallet .signet b.dir))
  check "declined restore: no backup of its own started" ((← b.app.controller.get).configuration.isNone && (← cloud.records.get).size == 1)
  -- the same restore, approved
  answer.set (Lean.Json.mkObj [("ok", true)])
  let m ← restore m
  check "approved restore: asked again, then restored" ((← prompts).size == 2 && m.onboarding.restored &&
    m.onboarding.restoreError == some "Restored. Network verification will resume when peers are reachable.")
    s!"{(← prompts)} {m.onboarding.restored} {m.onboarding.restoreError}"
  check "approved restore: the same wallet" ((← b.env.get).wallet.map (·.id) == some id)
  b.backend.stopNetworking
  WinnowApp.backendRef.set Backend.pending
  -- test mode: skipped, unless the run asks for the check
  let vars := [("WINNOW_E2E", "1"), ("WINNOW_E2E_ENTROPY", "04040404040404040404040404040404")]
  let mode (more : List (String × String)) : Option WinnowApp.E2E.Mode :=
    match WinnowApp.E2E.resolve (fun k => (vars ++ more).lookup k) with | .active m => some m | _ => none
  answer.set declined
  asked.set #[]
  WinnowApp.e2eRef.set (mode [])
  check "test mode: the check is skipped" (!(← fails (WinnowApp.authenticateNow fx "Restore")) && (← prompts).isEmpty)
  WinnowApp.e2eRef.set (mode [("WINNOW_E2E_DEVICE_AUTH", "1")])
  check "test mode with WINNOW_E2E_DEVICE_AUTH=1: asked, and declined it stops"
    ((← failsWith (WinnowApp.authenticateNow fx "Restore") "Canceled by user.") && (← prompts) == #["Restore"])
  -- approved, the authentication the shell kept is what the Keychain's reads that follow name
  let keeps : IO (Array Lean.Json) := do
    return (← asked.get).filterMap fun (n, a) => if n == "auth" then (a.getObjVal? "keep").toOption else none
  check "the check asks the shell to keep a yes, for a minute at most" ((← keeps) == #[Lean.toJson (60 : Nat)])
  Real.keychainContext.set none
  answer.set (Lean.Json.mkObj [("ok", true), ("context", "kept-9")])
  check "approved: the kept authentication is the one the reads name"
    (!(← fails (WinnowApp.authenticateNow fx "Restore")) && (← Real.keychainContext.get) == some "kept-9")
  answer.set (Lean.Json.mkObj [("ok", true)])
  check "approved by a shell that kept none: the reads name none"
    (!(← fails (WinnowApp.authenticateNow fx "Restore")) && (← Real.keychainContext.get).isNone)
  check "test mode: the secret is behind the person's presence only when the run asks"
    ((mode []).map (·.keychainProtection) == some false &&
     (mode [("WINNOW_E2E_KEYCHAIN_PROTECTION", "1")]).map (·.keychainProtection) == some true)
  WinnowApp.e2eRef.set none

def cloudEdgeCasesAndCloudAppTests (root : System.FilePath) : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  -- decode edge rejections: > maximumBytes, non-UTF8, bad UUID, unknown network, oversized sealedPhrase
  let oversized := ByteArray.mk (Array.replicate (CloudWalletBackup.maximumBytes + 1) 0x20)
  check "decode: > maximumBytes refused" (← refusedW (CloudWalletBackup.decode oversized))
  check "decode: non-UTF8 refused" (← refusedW (CloudWalletBackup.decode (ByteArray.mk #[0xFF, 0xFE])))
  let backup ← need "create backup" (CloudWalletBackup.create original key)
  let baseJson ← jsonOf backup
  check "decode: invalid UUID refused"
    (← refusedW (CloudWalletBackup.decode (bytesOfJson (baseJson.setObjVal! "id" (.str "not-a-uuid")))))
  check "decode: unknown network refused"
    (← refusedW (CloudWalletBackup.decode (bytesOfJson (baseJson.setObjVal! "network" (.str "signet2")))))
  let bigPhrase := Base64.encode (ByteArray.mk (Array.replicate (CloudWalletBackup.maximumSealedPhraseBytes + 1) 0))
  check "decode: oversized sealedPhrase refused"
    (← refusedW (CloudWalletBackup.decode (bytesOfJson (baseJson.setObjVal! "sealedPhrase" (.str bigPhrase)))))
  -- CloudWalletBackup.shared: v2 unread corrupt entries, Shared.walletID, lastKnownBlockHash, and v1 support
  let pub := { original with mnemonic := none, lastKnownBlockHash := some (String.ofList (List.replicate 64 'a')) }
  let pubJV := pub.toJV
  -- Inject corrupt vault & signer arrays into inner bundle object
  let innerObj := match pubJV with
    | .obj kvs => kvs.map fun (k, v) =>
      if k == "vaults" then (k, .arr #[.str "corrupt-vault"]) else (k, v)
    | _ => #[]
  let innerWithBad :=
    let hasVaults := innerObj.any (·.1 == "vaults")
    let xs := if hasVaults then innerObj else innerObj.push ("vaults", SwiftJSON.JV.arr #[SwiftJSON.JV.str "corrupt-vault"])
    let hasSigners := xs.any (·.1 == "signers")
    if hasSigners then xs else xs.push ("signers", SwiftJSON.JV.arr #[SwiftJSON.JV.str "corrupt-signer"])
  let customSealedJson := SwiftJSON.write (.obj #[("bundle", .obj innerWithBad)])
  let sealedWalletBad ← match ← AESGCM.sealRandom key customSealedJson.toUTF8
      (CloudWalletBackup.context backup.id backup.network (CloudWalletBackup.walletPurpose backup.savedAt)) with
    | .ok b => pure b.combined.get!
    | .error e => throw e.name
  let sharedRes ← need "shared with unread" ({ backup with sealedWallet := sealedWalletBad }.shared key)
  check "shared: counts corrupt vault + signer as unread and derives walletID + blockHash"
    (sharedRes.unread == 2 && sharedRes.walletID.isSome && sharedRes.lastKnownBlockHash.isSome)
  -- Shared.walletID without descriptor returns none
  check "Shared.walletID: none without descriptor" (({ sharedRes with descriptor := none }).walletID.isNone)
  -- v1 backup opens via shared
  let v1 ← legacyBackup original key backup.id backup.savedAt
  let v1Shared ← need "shared v1" (v1.shared key)
  check "shared: v1 backup decodes via shared" (v1Shared.lastKnownHeight == original.lastKnownHeight)
  -- unsupported version on state & shared
  let v3 := { backup with version := 3 }
  check "state/shared: version 3 refused"
    ((← refusedW (v3.state key)) && (← refusedW (v3.shared key)))
  -- identity mismatch in shared (wallet payload says mainnet for signet backup)
  let wrongNet := { pub with network := "mainnet" }
  let wrongSealed ← match ← AESGCM.sealRandom key (SwiftJSON.write (.obj #[("bundle", wrongNet.toJV)])).toUTF8
      (CloudWalletBackup.context backup.id backup.network (CloudWalletBackup.walletPurpose backup.savedAt)) with
    | .ok b => pure b.combined.get!
    | .error e => throw e.name
  check "shared: mismatched inner network refused"
    (← refusedW ({ backup with sealedWallet := wrongSealed }.shared key))
  -- Real.CloudApp.devicesText across all status shapes (empty, all read, >3 keyMissing, notOpened, notFetched, skipped)
  let t0 := ← Real.CloudApp.devicesText { listed := 0 } "5m"
  let tOk := ← Real.CloudApp.devicesText { listed := 1 } "2m"
  let manyMissing := #[1.0, 2.0, 3.0, 4.0].map fun d => (d, Real.Unread.keyMissing)
  let tMixed ← Real.CloudApp.devicesText
    { listed := 7, unread := manyMissing ++ #[(5.0, .notOpened), (6.0, .notFetched)], skipped := 2 } "10m"
  let tSingular ← Real.CloudApp.devicesText
    { listed := 2, unread := #[(1.0, .notOpened)], skipped := 1 } "1m"
  check "devicesText covers all branches"
    (contains t0 "no other backup" &&
     contains tOk "in step with 1 backup" &&
     contains tMixed "and 1 more" && contains tMixed "did not hand over 1 backup" && contains tMixed "2 accounts or signers" &&
     contains tSingular "1 account or signer in those backups is")
  -- CloudApp with allows=false / restore guards
  let pDisabled ← cloudPhone root "disabled-cloud" (← newKeys) false
  pDisabled.bootExisting
  pDisabled.app.discover
  pDisabled.app.scheduleBackup
  pDisabled.app.prepare "abandon"
  pDisabled.app.schedulePreparation
  check "CloudApp: allows=false keeps controller disabled" (!(← pDisabled.app.controller.get).enabled)
  check "CloudApp.restore fails cleanly when wallet is open or !allows"
    (← cloudFails (pDisabled.app.restore .signet pDisabled.dir "no-such-id"))

def main (args : List String) : IO UInt32 := runMain "cloud-backup-test" do
  let writeDir := match args with | "--write" :: d :: _ => some d | _ => none
  runTest "roundTripRestoresSigningAndAddressCounters" roundTripRestoresSigningAndAddressCounters
  runTest "automaticUpdateKeepsTheSealedKeyAndNewHistoryFrontier" automaticUpdateKeepsTheSealedKeyAndNewHistoryFrontier
  runTest "wrongKeyAndModifiedMetadataAreRejected" wrongKeyAndModifiedMetadataAreRejected
  runTest "appContextIsEncryptedAndUpdatesWithoutReadingThePhrase" appContextIsEncryptedAndUpdatesWithoutReadingThePhrase
  runTest "legacyBackupRestoresAndUpgradesWithoutLosingItsKey" legacyBackupRestoresAndUpgradesWithoutLosingItsKey
  runTest "mismatchedWalletAndMissingPhraseAreRefused" mismatchedWalletAndMissingPhraseAreRefused
  runTest "cloudBackupRestores" cloudBackupRestores
  runTest "cloudContextRoundTrips" cloudContextRoundTrips
  runTest "existingContactsAndNewerPaymentCounterSurviveRestore" existingContactsAndNewerPaymentCounterSurviveRestore
  runTest "wrongNetworkOrMalformedLabelsAreRejectedBeforeStoreChanges" wrongNetworkOrMalformedLabelsAreRejectedBeforeStoreChanges
  runTest "swiftVectors" (swiftVectors writeDir)
  runTest "controller" controllerTests
  runTest "onboardingScreens" onboardingScreens
  runTest "shellAnswers" shellAnswers
  runTest "shellAdapters" shellAdapters
  let root ← IO.FS.createTempDir
  runTest "storeKeysOutOfPresence" (storeKeysOutOfPresence root)
  runTest "automaticCloud" (automaticCloudTests root)
  runTest "scopedPreparation" (scopedPreparationTests root)
  runTest "restoreFromICloud" (restoreFromICloud root)
  runTest "secondWalletFromICloud" (secondWalletFromICloud root)
  runTest "declinedDeviceCheck" (declinedDeviceCheck root)
  runTest "cloudEdgeCasesAndCloudAppTests" (cloudEdgeCasesAndCloudAppTests root)
  try IO.FS.removeDirAll root catch _ => pure ()
