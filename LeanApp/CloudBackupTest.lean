import WinnowApp.Real.CloudAppState
import WinnowApp.Real
import WinnowApp.View
import WinnowApp.E2E
import LeanNative.Erase
import LeanNative.Json
import Lean.Data.Json

/-! `cloud-backup-test`: the encrypted iCloud recovery formats, headless.

* upstream d2ca878's `CloudWalletBackupTests` (all six), `CloudAppStateTests` (all three) and the restore
  halves of `CloudBackupTests` (what a backup restores, and the digest an automatic update compares);
  the controller around them (iCloud Keychain, CloudKit, scheduling) needs the shell and is not here;
* `../Lean/Vectors/cloud-backup.json`, written by upstream's `CloudWalletBackup.swift` (verbatim, over a
  copy of d2ca878's WalletCore): its version 1 and version 2 backups open here, its `wallet-…` purposes
  and the backup digest (and the canonical JSON under it) match byte for byte.

`--write <dir>` also leaves a Lean-made backup (`lean-backup.json`) and its key (`lean-backup.key`) there for
the Swift side to open. Run from `LeanApp/`. Exits 1 on any failure. -/

open Winnow WinnowApp WinnowApp.RecordsReal Keys
open Tx (BitcoinNetwork)

initialize passed : IO.Ref Nat ← IO.mkRef 0
initialize failures : IO.Ref (Array String) ← IO.mkRef #[]

def check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then passed.modify (· + 1)
  else
    failures.modify (·.push name)
    IO.println s!"FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"

abbrev TM := ExceptT String IO

def wm {α} (name : String) (x : WM α) : TM α := do
  match ← x.run with
  | .ok a => pure a
  | .error e => throw s!"{name}: {e.name}"

def rm {α} (name : String) (x : RM α) : TM α := do
  match ← x.run with
  | .ok a => pure a
  | .error e => throw s!"{name}: {e.name}: {e.description}"

def refusedW {α} (x : WM α) : IO Bool := do return (← x.run).toOption.isNone
def refusedR {α} (x : RM α) : IO Bool := do return (← x.run).toOption.isNone

def runTest (name : String) (t : TM Unit) : IO Unit := do
  match ← t.run with
  | .ok () => pure ()
  | .error msg =>
    failures.modify (·.push name)
    IO.println s!"FAIL {name} (aborted): {msg}"

def newKeys : IO (KeyStore IO) := do return inMemoryKeyStore (← IO.mkRef {})

def walletBundle (network : BitcoinNetwork) (fill : UInt8) : TM ImportBundle := do
  let w ← wm "create" (Wallet.create network (← newKeys) none (some (ByteArray.mk (Array.replicate 16 fill))) 100)
  wm "export" (w.exportBundle (includeMnemonic := true))

def randomKey : IO ByteArray := IO.getRandomBytes 32

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

def jsonOf (b : CloudWalletBackup) : TM Lean.Json := do
  let text := String.fromUTF8! (← wm "encode" b.encoded)
  match Lean.Json.parse text with | .ok j => pure j | .error e => throw e

def bytesOfJson (j : Lean.Json) : ByteArray := j.compress.toUTF8

/-! ## CloudWalletBackupTests -/

def roundTripRestoresSigningAndAddressCounters : TM Unit := do
  let original := { (← walletBundle .signet 7) with nextReceiveIndex := some 19, nextChangeIndex := some 8 }
  let key ← randomKey
  let encrypted ← wm "create" (CloudWalletBackup.create original key)
  let data ← wm "encode" encrypted.encoded
  check "round trip: the file does not hold the words" (!contains (String.fromUTF8! data) original.mnemonic.get!)
  let restored ← wm "restore" ((← wm "decode" (CloudWalletBackup.decode data)).restoredBundle key)
  check "round trip: the bundle comes back whole" (restored == original)
  let keys ← newKeys
  let wallet ← wm "import" (Wallet.importing restored keys)
  check "round trip: importing it stores the words" (match ← (keys.load wallet.id).run with
    | .ok s => s == .mnemonic original.mnemonic.get! | .error _ => false)

def automaticUpdateKeepsTheSealedKeyAndNewHistoryFrontier : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  let first ← wm "create" (CloudWalletBackup.create original key)
  let next := { original with mnemonic := none, lastKnownHeight := 123, nextReceiveIndex := some 5 }
  let updated ← wm "update" (first.updating next key)
  check "update: the phrase box is kept" (updated.sealedPhrase == first.sealedPhrase)
  let restored ← wm "restore" (updated.restoredBundle key)
  check "update: the words, the new frontier and the new cursor"
    (restored.mnemonic == original.mnemonic && restored.lastKnownHeight == 123 && restored.nextReceiveIndex == some 5)

def wrongKeyAndModifiedMetadataAreRejected : TM Unit := do
  let key ← randomKey
  let original ← walletBundle .signet 7
  let backup ← wm "create" (CloudWalletBackup.create original key)
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
  let first ← wm "create" (CloudWalletBackup.create original key (appState := some metadata))
  check "app data: not in the clear" (!contains (String.fromUTF8! (← wm "encode" first.encoded)) "invoice label")
  check "app data: restored" ((← wm "app state" (first.restoredAppState key)) == some metadata)
  let publicBundle := { original with mnemonic := none }
  let edited := "edited local notes".toUTF8
  let second ← wm "update" (first.updating publicBundle key (appState := some edited))
  check "app data: the phrase box is kept" (second.sealedPhrase == first.sealedPhrase)
  check "app data: replaced" ((← wm "app state" (second.restoredAppState key)) == some edited)
  check "app data: the bundle is unchanged" ((← wm "restore" (second.restoredBundle key)) == original)
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
  let loaded ← wm "decode" (CloudWalletBackup.decode (← wm "encode" legacy.encoded))
  check "legacy: restores" ((← wm "restore" (loaded.restoredBundle key)) == original)
  check "legacy: has no app data" ((← wm "app state" (loaded.restoredAppState key)) == none)
  let upgraded ← wm "upgrade" (loaded.updating { original with mnemonic := none } key (appState := some "notes".toUTF8))
  check "legacy: upgrades to version 2 with its phrase box" (upgraded.version == 2 && upgraded.sealedPhrase == legacy.sealedPhrase)
  check "legacy: the upgrade restores" ((← wm "restore" (upgraded.restoredBundle key)) == original &&
    (← wm "app state" (upgraded.restoredAppState key)) == some "notes".toUTF8)
  let downgraded := bytesOfJson ((← jsonOf upgraded).setObjVal! "version" (1 : Nat))
  check "legacy: a version 2 box called version 1 does not restore"
    (← refusedW (do (← CloudWalletBackup.decode downgraded).restoredBundle key))

def mismatchedWalletAndMissingPhraseAreRefused : TM Unit := do
  let original ← walletBundle .signet 7
  let key ← randomKey
  let backup ← wm "create" (CloudWalletBackup.create original key)
  let other := { original with descriptor := some "different wallet" }
  check "mismatch: another wallet does not update it" (← refusedW (backup.updating other key))
  check "mismatch: no words, no backup" (← refusedW (CloudWalletBackup.create { other with mnemonic := none } key))
  check "mismatch: past 32 MiB does not decode"
    (← refusedW (CloudWalletBackup.decode (ByteArray.mk (Array.replicate (CloudWalletBackup.maximumBytes + 1) 0))))

/-! ## CloudBackupTests (the restore halves) -/

def cloudBackupRestores : TM Unit := do
  let bundle ← walletBundle .signet 9
  let key ← randomKey
  let first ← wm "enable" (CloudWalletBackup.create bundle key (appState := some "before".toUTF8))
  let watchOnly := { bundle with mnemonic := none }
  let before : CloudBackupContents := { bundle := watchOnly, appState := some "before".toUTF8 }
  let after : CloudBackupContents := { bundle := watchOnly, appState := some "after".toUTF8 }
  check "contents: only changing the app data changes the digest" (before.digest != after.digest)
  check "contents: the words are not part of the digest"
    (({ before with bundle := bundle } : CloudBackupContents).digest == before.digest)
  let second ← wm "update" (first.updating watchOnly key (appState := after.appState))
  check "contents: the app data and the whole bundle restore"
    ((← wm "app state" (second.restoredAppState key)) == some "after".toUTF8 &&
     (← wm "restore" (second.restoredBundle key)) == bundle)

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

def peopleStore (dir : System.FilePath) : TM PeopleStore := do
  let vault := StoreKeyVault.inMemory (← IO.mkRef {})
  let (s, _) ← PeopleStore.configure vault (some (dir / "people.json")) .mainnet
  return s

def cloudContextRoundTrips : TM Unit := do
  let f ← fixture
  let restored ← match ← rm "decode" (CloudAppState.decode (some f.state.encoded) f.bundle) with
    | some r => pure r | none => throw "no context"
  check "context: round trips" (restored == f.state)
  let vault := StoreKeyVault.inMemory (← IO.mkRef {})
  let (people, _) ← PeopleStore.configure vault (some (f.dir / "people.json")) .mainnet
  let plan ← rm "plan" (people.planRestore restored.people)
  let people ← rm "restore" (people.restore vault writeAtomically plan)
  check "context: the address book restores" ((← rm "backup" people.backup) == f.state.people)
  let labels ← LabelStore.open (some (f.dir / "labels.json")) "restored" .mainnet
  let labels ← rm "labels restore" (labels.restore writeAtomically restored.receiveLabels)
  let sorted (xs : Array (String × String)) := (xs.toList.mergeSort fun a b => !(b.1 < a.1)).toArray
  check "context: the receive notes restore" (sorted (← rm "labels backup" labels.backup) == sorted f.state.receiveLabels)
  let reopened ← LabelStore.open (some (f.dir / "labels.json")) "restored" .mainnet
  check "context: the receive notes are on disk" (sorted (← rm "reopened" reopened.backup) == sorted f.state.receiveLabels)
  check "context: the manual export stays without the address book" (!contains f.bundle.serialized "Saved friend")
  check "context: older backups have none" ((← rm "none" (CloudAppState.decode none f.bundle)).isNone)

def existingContactsAndNewerPaymentCounterSurviveRestore : TM Unit := do
  let f ← fixture
  let vault := StoreKeyVault.inMemory (← IO.mkRef {})
  let (store, _) ← PeopleStore.configure vault (some (f.dir / "people.json")) .mainnet
  let p := f.state.people.people[0]!
  let mine : PeopleStore.Backup :=
    { people := #[{ p with id := ← UUIDText.random, name := "Current local name", nextPaymentIndex := 24 }], senderByTxid := #[] }
  let store ← rm "restore local" (store.restore vault writeAtomically mine)
  let merged ← rm "plan" (store.planRestore f.state.people)
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
  let store ← rm "restore" (store.restore vault writeAtomically f.state.people)
  let invalid := { f.state.people with
    senderByTxid := f.state.people.senderByTxid.push (String.join (List.replicate 32 "02"), "unknown person") }
  check "context: a dangling sender name fails validation" (← refusedR (store.planRestore invalid))
  check "context: the store is unchanged" ((← rm "backup" store.backup) == f.state.people)

/-! ## Swift's own output (`Vectors/cloud-backup.json`) -/

def swiftVectors (writeDir : Option String) : TM Unit := do
  let text ← IO.FS.readFile "../Lean/Vectors/cloud-backup.json"
  let j ← match Lean.Json.parse text with | .ok j => pure j | .error e => throw e
  let str (k : String) : TM String := match j.getObjValAs? String k with | .ok s => pure s | .error e => throw e
  let bundle ← match ImportBundle.decode (← str "bundle") with | .ok b => pure b | .error e => throw e.name
  let key := ofHex! (← str "key")
  let appState := ofHex! (← str "appState")
  let v2 ← wm "swift v2" (CloudWalletBackup.decode (← str "v2").toUTF8)
  check "swift v2: restores the bundle" ((← wm "restore" (v2.restoredBundle key)) == bundle)
  check "swift v2: restores the app data" ((← wm "app state" (v2.restoredAppState key)) == some appState)
  check "swift v2: savedAt and the id read back" (v2.savedAt == 783_000_000.123456 && (UUIDText.canonical? v2.id) == some v2.id)
  let plain ← wm "swift v2 plain" (CloudWalletBackup.decode (← str "v2NoAppState").toUTF8)
  check "swift v2 without app data" ((← wm "restore" (plain.restoredBundle key)) == bundle &&
    (← wm "app state" (plain.restoredAppState key)).isNone)
  let v1 ← wm "swift v1" (CloudWalletBackup.decode (← str "v1").toUTF8)
  check "swift v1: restores" (v1.version == 1 && (← wm "restore" (v1.restoredBundle key)) == bundle &&
    (← wm "app state" (v1.restoredAppState key)).isNone)
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
    let mine ← wm "create" (CloudWalletBackup.create bundle key (appState := some appState))
    IO.FS.writeBinFile (System.FilePath.mk dir / "lean-backup.json") (← wm "encode" mine.encoded)
    IO.FS.writeFile (System.FilePath.mk dir / "lean-backup.key") (hex key)
    IO.println s!"  wrote {dir}/lean-backup.json"

def waitUntil (ms : Nat) (cond : IO Bool) : IO Bool := do
  let deadline := (← IO.monoMsNow) + ms
  repeat
    if ← cond then return true
    if (← IO.monoMsNow) ≥ deadline then return false
    IO.sleep 10
  return false

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
  let w ← wm "create" (Wallet.create .signet (← newKeys) none (some (ByteArray.mk (Array.replicate 16 9))) 100)
  controller.configure (some dir) (some "test-wallet")
  return { controller, cloud, bundle := ← wm "export" (w.exportBundle (includeMnemonic := true)), dir }

def failsWith {α} (x : IO α) (text : String) : IO Bool := do
  match ← x.toBaseIO with
  | .ok _ => return false
  | .error e => return toString e == text

def fails {α} (x : IO α) : IO Bool := do return (← x.toBaseIO) matches .error _

open Real in
def controllerTests : TM Unit := do
  -- testNoUploadUntilPreparedAndStopKeepsCloudCopy
  let f ← ctlFixture
  let asked ← IO.mkRef false
  f.controller.update (do asked.set true; return { bundle := f.bundle })
  check "no upload until prepared" (!(← asked.get) && (← f.cloud.count) == 0)
  f.controller.enable f.bundle (walletID := "test-wallet")
  check "enabled once prepared" (← f.controller.get).enabled
  f.controller.stop
  check "stop keeps the iCloud copy" (!(← f.controller.get).enabled && (← f.cloud.count) == 1)
  -- testFailedUploadKeepsLastSuccessfulBackup
  let f ← ctlFixture
  f.controller.enable f.bundle (walletID := "test-wallet")
  let saved := (← f.controller.get).lastSaved
  f.cloud.failing.set true
  let updated := { f.bundle with mnemonic := none, nextReceiveIndex := some 7 }
  check "a failed upload is not treated as saved" (← fails (f.controller.update (pure { bundle := updated })))
  check "the last successful save stays" ((← f.controller.get).lastSaved == saved)
  f.cloud.failing.set false
  f.controller.discover "signet"
  match (← f.controller.get).available[0]? with
  | some b => check "the last successful backup restores" ((← f.controller.restore b.id) == f.bundle)
  | none => check "the backup is listed" false
  -- testReconfigureSameWalletDoesNotCancelBackup
  let f ← ctlFixture
  f.controller.configure (some f.dir) (some "test-wallet")
  f.controller.enable f.bundle (walletID := "test-wallet")
  f.controller.configure (some f.dir) (some "test-wallet")
  check "reconfiguring the same wallet keeps the backup" (← f.controller.get).enabled
  f.controller.configure (some f.dir) (some "another-wallet")
  check "another wallet has none" (!(← f.controller.get).enabled)
  -- testCancelledExportCannotUploadToAnotherWallet
  let f ← ctlFixture
  f.controller.enable f.bundle (walletID := "test-wallet")
  let switched := f.controller.update do
    f.controller.configure (some f.dir) (some "another-wallet")
    return { bundle := { f.bundle with nextReceiveIndex := some 8 } }
  check "a wallet change cancels the export" (← failsWith switched cancelledText)
  check "nothing uploaded for the other wallet" ((← f.cloud.saves.get) == 1 && !(← f.controller.get).enabled)
  -- testChangedAccountCannotOverwriteExistingBackup
  let f ← ctlFixture
  f.controller.enable f.bundle (walletID := "test-wallet")
  f.cloud.accountName.set "second-account"
  check "a changed account cannot overwrite the backup"
    (← failsWith (f.controller.update (pure { bundle := { f.bundle with nextReceiveIndex := some 6 } })) CloudBackupError.accountChanged.description)
  check "one save only" ((← f.cloud.saves.get) == 1)
  -- testLateUploadCannotEnableBackupAfterWalletChange
  let f ← ctlFixture
  let gate ← IO.Promise.new
  f.cloud.hold.set (some gate)
  let enable ← IO.asTask (f.controller.enable f.bundle (walletID := "test-wallet"))
  discard <| waitUntil 2000 f.cloud.holding.get
  f.controller.configure (some f.dir) (some "another-wallet")
  gate.resolve ()
  check "a late acknowledgement is cancelled" (match ← IO.wait enable with | .error e => toString e == cancelledText | .ok _ => false)
  check "it enables nothing" (!(← f.controller.get).enabled && (← f.controller.get).lastSaved.isNone)
  let reopened ← CloudBackupController.new f.cloud.store (← memoryCloudKeys)
  reopened.configure (some f.dir) (some "another-wallet")
  check "the encrypted retry does not configure a different wallet" (!(← reopened.get).enabled)
  -- testOnlyChangingAppContextStillUpdatesBackup
  let f ← ctlFixture
  f.controller.enable f.bundle (some "before".toUTF8) "test-wallet"
  f.controller.update (pure { bundle := { f.bundle with mnemonic := none }, appState := some "after".toUTF8 })
  check "the context alone changing uploads again" ((← f.cloud.saves.get) == 2)
  f.controller.discover "signet"
  match (← f.controller.get).available[0]? with
  | some b =>
    let r ← f.controller.restoreContents b.id
    check "the new context restores" (r.contents.appState == some "after".toUTF8)
    check "with the words carried forward" (r.contents.bundle == f.bundle)
  | none => check "the backup is listed" false
  -- testRestoredDeviceResumesBackupsAcrossOfflineRelaunchWithoutOverwritingOriginal
  let f ← ctlFixture
  f.controller.enable f.bundle (walletID := "test-wallet")
  f.controller.discover "signet"
  let some source := (← f.controller.get).available[0]? | throw "no backup listed"
  let restored ← f.controller.restoreContents source.id
  let keys ← memoryCloudKeys
  let replacement := f.dir / "replacement"
  IO.FS.createDirAll replacement
  let device ← CloudBackupController.new f.cloud.store keys
  device.configure (some replacement) (some "test-wallet")
  device.resume restored.contents "test-wallet" restored.account
  check "resume: enabled, not yet acknowledged" ((← device.get).enabled && (← device.get).lastSaved.isNone)
  f.cloud.failing.set true
  check "resume: an offline save fails" (← fails (device.update (pure { bundle := f.bundle })))
  check "resume: still enabled, still not saved" ((← device.get).enabled && (← device.get).lastSaved.isNone)
  let relaunched ← CloudBackupController.new f.cloud.store keys
  relaunched.configure (some replacement) (some "test-wallet")
  check "resume: the retry survives a relaunch" ((← relaunched.get).enabled && (← relaunched.get).lastSaved.isNone)
  f.cloud.failing.set false
  relaunched.update (pure { bundle := f.bundle })
  check "resume: saved once online" (← relaunched.get).lastSaved.isSome
  check "resume: the replacement phone has its own record" ((← f.cloud.count) == 2)
  check "resume: the original backup is untouched" ((← f.controller.restore source.id) == f.bundle)
  -- testAutomaticDefaultAndOptOutSurviveRestartAndWalletChanges
  let f ← ctlFixture
  check "automatic by default, not backed up" ((← f.controller.get).automaticEnabled && (← f.controller.get).statusTitle == "Not backed up")
  f.controller.prepare { bundle := f.bundle } "test-wallet"
  check "prepared: backing up" ((← f.controller.get).statusTitle == "Backing up")
  f.controller.stop
  let reopened ← CloudBackupController.new f.cloud.store (← memoryCloudKeys)
  reopened.configure (some f.dir) (some "test-wallet")
  check "the opt-out survives a restart" (!(← reopened.get).automaticEnabled)
  reopened.prepare { bundle := f.bundle } "test-wallet"
  check "an opted-out wallet prepares nothing" (!(← reopened.get).enabled)
  reopened.configure (some f.dir) (some "new-wallet")
  check "a new wallet is automatic" (← reopened.get).automaticEnabled
  reopened.configure (some f.dir) (some "test-wallet")
  check "the opted-out wallet stays off" (!(← reopened.get).automaticEnabled)
  reopened.setAutomatic true
  check "turned on again, it needs preparation" (← reopened.get).needsPreparation
  -- testOfflineInitialPreparationDoesNotRequireAnAccountOrClaimSuccess
  let f ← ctlFixture
  f.cloud.failing.set true
  f.controller.prepare { bundle := f.bundle } "test-wallet"
  check "offline preparation: enabled, not saved" ((← f.controller.get).enabled && (← f.controller.get).lastSaved.isNone)
  check "offline: the upload fails" (← fails (f.controller.update (pure { bundle := f.bundle })))
  check "offline: still not saved" (← f.controller.get).lastSaved.isNone
  f.cloud.failing.set false
  f.controller.update (pure { bundle := f.bundle })
  check "online: backed up" ((← f.controller.get).statusTitle == "Backed up")
  -- testScheduledFailuresBackOffWithoutDroppingAutomaticPreference
  let f ← ctlFixture
  f.controller.prepare { bundle := f.bundle } "test-wallet"
  f.cloud.failing.set true
  f.controller.schedule (pure { bundle := f.bundle })
  discard <| waitUntil 8000 do return (← f.controller.get).message.isSome
  let st ← f.controller.get
  check "a scheduled failure says so" st.message.isSome
  check "the automatic preference stays" (st.automaticEnabled && st.statusTitle == "Not backed up")
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
  original.enable f.bundle (walletID := "test-wallet")
  let waiting ← CloudBackupController.new f.cloud.store (← memoryCloudKeys)
  waiting.discover "signet"
  let some b := (← waiting.get).available[0]? | throw "no backup listed"
  check "a new installation waits for the key" (← failsWith (waiting.restore b.id) CloudBackupError.keyUnavailable.description)
  let later ← CloudBackupController.new f.cloud.store shared
  later.discover "signet"
  check "once the key arrives it restores" ((← later.restore b.id) == f.bundle)
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
    (cloudKeys : Option CloudBackupKeys := none) (whileAuthenticating : IO Unit := pure ()) : TM CloudPhone := do
  let vars := [("WINNOW_E2E", "1"), ("WINNOW_E2E_RUN", "cloud"), ("WINNOW_E2E_ENTROPY", "04040404040404040404040404040404"),
               ("WINNOW_E2E_PEER", "127.0.0.1:1"), ("WINNOW_E2E_CHALLENGE", "51")]
  let .active mode := WinnowApp.E2E.resolve (fun k => vars.lookup k) | throw "test mode did not resolve"
  let cloud ← match cloud with | some c => pure c | none => MemoryCloud.new
  let cloudKeys ← match cloudKeys with | some k => pure k | none => memoryCloudKeys
  let attempts ← IO.mkRef 0
  let deps : Deps := { keyStore := keys, fetch := fun _ => throw (.other "offline"), networkParams := mode.networkParams, peerCount := 1 }
  let (backend, env, app) ← Backend.realWithCloud deps (store := cloud.store) (keys := cloudKeys)
    (authenticate := fun _ => do
      attempts.modify (· + 1)
      whileAuthenticating
      unless auth do throw (IO.userError "Authentication was denied."))
    (scheduleDelayMs := 50)
  let dir := (root / name / "signet").toString
  IO.FS.createDirAll dir
  let settings : Settings := { network := .signet, signet := { manualPeers := ["127.0.0.1:1"] } }
  return { backend, env, app, cloud, keys, dir, settings, authAttempts := attempts }

/-- Boot with a wallet already on disk, scene active. -/
def CloudPhone.bootExisting (p : CloudPhone) : TM Unit := do
  discard <| wm "create" (Wallet.create .signet p.keys (some (System.FilePath.mk p.dir / "wallet.json")) (some (ByteArray.mk (Array.replicate 16 4))))
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
  discard <| waitUntil 3000 do return (← p.app.controller.get).message.isSome
  check "declined: one authentication prompt" ((← p.authAttempts.get) == 1)
  check "declined: not backed up" ((← p.backend.cloudStatus).statusTitle == "Not backed up")
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
  discard <| waitUntil 3000 do return (← p.app.controller.get).message.isSome
  let st ← p.backend.cloudStatus
  check "unavailable iCloud: no authentication prompt" ((← p.authAttempts.get) == 0)
  check "unavailable iCloud: says so, not backed up, still automatic"
    (st.message == some Real.CloudBackupError.unavailable.description && st.statusTitle == "Not backed up" && st.automaticEnabled)
  let manual ← match ImportBundle.decode (← p.backend.exportBundle false) with
    | .ok b => pure b | .error _ => throw "the manual export does not decode"
  check "unavailable iCloud: the manual export still works, without the words" (manual.network == "signet" && manual.mnemonic.isNone)
  p.backend.cloudScene false
  p.backend.stopNetworking
  -- testModeChangesDoNotUndoExplicitBackupOptOut
  let p ← cloudPhone root "optout" (← newKeys) false
  p.bootExisting
  p.backend.setAutomaticCloudBackup false
  p.backend.updateSettings { p.settings with advancedMode := true }
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
  check "creation lands on the wallet, with no checklist" (model.stage == .ready && model.walletID == some id && model.sheets.isEmpty)

/-- Restore from iCloud end to end: phone A's backup (people included) restores on phone B, which then keeps
its own record bound to the same account. -/
def restoreFromICloud (root : System.FilePath) : TM Unit := do
  let cloud ← Real.MemoryCloud.new
  let sharedKeys ← Real.memoryCloudKeys
  let a ← cloudPhone root "restoreA" (← newKeys) true (some cloud) (some sharedKeys)
  discard <| a.backend.openWallet .signet a.dir
  a.activate
  let id ← a.backend.createWallet .signet a.dir
  let bob ← wm "bob" (Wallet.create .signet (← newKeys) none (some (ByteArray.mk (Array.replicate 16 0xB0))))
  let card ← match ← (RecordsReal.ownPersonCard bob "Bob").run with
    | .ok c => pure c.serialized | .error _ => throw "card"
  discard <| a.backend.addPerson "Bob" (some card) none none none
  a.backend.updateSettings { a.settings with ownDisplayName := "Alice", advancedMode := true }
  a.app.controller.update do
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
  let (restoredID, verified, context) ← b.backend.restoreCloudBackup .signet b.dir backup.id
  check "restore: the same wallet" (restoredID == id)
  check "restore: one authentication" ((← b.authAttempts.get) == 1)
  check "restore: no peer yet, verification waits" verified.isNone
  check "restore: the display name and Advanced switch come back" (context == some ("Alice", true))
  check "restore: saved people come back" ((← b.backend.records).people.any (·.name == "Bob"))
  let st ← b.app.controller.get
  check "restore: this phone keeps its own backup, bound to the account" (st.enabled && st.lastSaved.isNone &&
    (st.configuration.bind (·.account)) == some "first-account" && (st.configuration.map (·.backup.id)) != some backup.id)
  check "restore: a second restore is refused" (← fails (b.backend.restoreCloudBackup .signet b.dir backup.id))
  b.backend.stopNetworking

/-! ## The screens: onboarding without a checklist, Simple's backup line, Advanced's iCloud controls -/

def rendered (h : H) : String := (LeanNative.Html.toWire h).toJson.compress

def onboardingScreens : TM Unit := do
  let m : Model := { stage := .onboarding, active := true }
  let plain := rendered (view m)
  check "onboarding: no phrase checklist" (!contains plain "writtenDownToggle" && !contains plain "I have written the words down")
  check "onboarding: create and restore from a file" (contains plain "createWalletButton" && contains plain "importWalletButton" &&
    contains plain "Restore from a file")
  check "onboarding: iCloud said up front" (contains plain "automatically backs up your wallet with iCloud when available")
  check "onboarding: no iCloud restore without a backup" (!contains plain "restoreCloudBackupButton")
  check "onboarding: no network picker in Simple mode on mainnet" (!contains plain "onboardingNetworkPicker")
  let found := rendered (view { m with cloud := { available := [{ id := "A", savedAtText := "10/27/2026, 7:28 PM" }] } })
  check "onboarding: a saved backup offers the iCloud restore" (contains found "restoreCloudBackupButton" && contains found "1 saved backup(s) found.")
  let (m2, cs) := step (.cloud .openRestore) { m with cloud := { available := [{ id := "A", savedAtText := "10/27/2026, 7:28 PM" }] } }
  check "onboarding: the restore sheet looks again" (m2.hasSheet .cloudRestore && cs.any (· matches .discoverCloud))
  let sheet := rendered (view m2)
  check "restore sheet: lists the backup by date" (contains sheet "Choose a saved backup" && contains sheet "10/27/2026, 7:28 PM")
  let (m3, cs) := step (.cloud (.restore "A")) m2
  check "restore sheet: restoring" (m3.onboarding.restoring && cs.any (· matches .restoreCloud ..))
  let (m4, cs) := onHost (.cloudRestored m3.generation "W" none (some ("Alice", true))) m3
  check "restore sheet: restored, with the context's settings saved" (m4.onboarding.restored && m4.settings.ownDisplayName == "Alice" &&
    m4.settings.advancedMode && cs.any (· matches .saveSettings _))
  check "restore sheet: says verification waits for peers"
    (contains (rendered (view m4)) "Restored. Network verification will resume when peers are reachable.")
  let (m5, _) := step .finishOnboarding m4
  check "restore sheet: Continue lands on the wallet" (m5.stage == .ready && m5.sheets.isEmpty)
  let signet := rendered (view { m with settings := { network := .signet } })
  check "onboarding: a signet wallet keeps the network picker" (contains signet "onboardingNetworkPicker")
  -- Simple mode's backup line
  let home (c : CloudStatus) := rendered (.list (beginnerSections { stage := .ready, cloud := c, walletID := some "w" }) : H)
  let notYet := home {}
  check "Simple: not backed up offers the backup file" (contains notYet "Not backed up" && contains notYet "backupButton" &&
    contains notYet "Your wallet still works. Until iCloud backup works, keep a backup file yourself." &&
    contains notYet "Save a backup file")
  let noEntitlement := home { message := some cloudMissingEntitlementText }
  check "Simple: a build without iCloud says so once" (contains noEntitlement "iCloud backup isn't available in this build of Winnow." &&
    (noEntitlement.splitOn "Not backed up").length == 2 && !contains noEntitlement "Sign in to iCloud")
  let done := home { statusTitle := "Backed up", lastSavedText := some "10/27/2026, 7:28 PM", enabled := true }
  check "Simple: backed up, with its date, and no manual nag" (contains done "Last saved 10/27/2026, 7:28 PM" && !contains done "backupButton")
  -- the backup section: the iCloud controls and the words are Advanced's
  let simpleBackup := rendered (backupSection { walletID := some "w" })
  check "Simple's Back up page: only the file" (contains simpleBackup "exportBundleButton" && !contains simpleBackup "revealPhraseButton" &&
    !contains simpleBackup "iCloud backup")
  let advanced : Model := { walletID := some "w", settings := { advancedMode := true } }
  let advBackup := rendered (backupSection advanced)
  check "Advanced: iCloud backup and the recovery phrase" (contains advBackup "iCloud backup" && contains advBackup "revealPhraseButton")
  check "Settings: the plain footer and button" (contains advBackup "iCloud backup keeps this wallet automatically. A backup file is a copy you keep yourself." &&
    contains advBackup "Save a backup file" && !contains advBackup "Back up wallet")
  check "Simple's Back up page: the file, in plain words" (contains simpleBackup "A backup file is a copy of this wallet you keep yourself." &&
    contains simpleBackup "Save a backup file")
  let row (c : CloudStatus) := rendered (backupSection { advanced with cloud := c })
  check "Settings row: backed up, how long ago" (contains (row { statusTitle := "Backed up", lastSavedAgo := some "5 min" }) "Backed up 5 min ago")
  check "Settings row: not available in this build" (contains (row { message := some cloudMissingEntitlementText }) "Not available")
  check "Settings row: off" (contains (row { automaticEnabled := false }) "\"Off\"")
  let (sheetModel, _) := step (.backup .openExport) advanced
  let exportText := rendered (exportSheet sheetModel [])
  check "Backup file sheet: its title and what it does" (contains exportText "Backup file" && !contains exportText "Back up wallet" &&
    contains exportText "Saves a file you can keep in Files or send to yourself. Restore it from Restore from a file." &&
    contains exportText "Without the recovery phrase the file restores your history but not the ability to spend.")
  let (asking, _) := step (.backup .createExport) { sheetModel with exportState := { includeMnemonic := true } }
  check "Backup file sheet: the phrase still asks first" (asking.confirm == some .exportWithPhrase)
  let (m6, _) := step (.cloud .openBackup) advanced
  let controls := rendered (cloudBackupSheet m6 [])
  check "Advanced: the automatic switch" (contains controls "automaticCloudBackupToggle" && contains controls "Automatic iCloud backup")
  check "Advanced: the switch asks the backend" ((step (.cloud (.setAutomatic false)) m6).2.any (· matches .setAutomaticCloud false))

/-- The shell's CloudKit answers as the screens' texts: a build without the entitlement is not a sign-in
problem (PORT.md, deliberate departures, user 2026-10-28). -/
def shellAnswers : TM Unit := do
  let answering (answer : Lean.Json) : Real.Ask := fun _ _ => pure (Task.pure answer)
  let accountText (answer : Lean.Json) : IO String := do
    match ← ((Real.shellCloudStore (answering answer)).account).toBaseIO with
    | .ok _ => return "ok"
    | .error e => return toString e
  check "missingEntitlement: its own text"
    ((← accountText (Lean.Json.mkObj [("error", Lean.Json.str "missingEntitlement")])) == "iCloud backup isn't available in this build of Winnow.")
  check "notAuthenticated: sign in"
    ((← accountText (Lean.Json.mkObj [("error", Lean.Json.str "notAuthenticated")])) == Real.CloudBackupError.unavailable.description)
  check "no account: sign in"
    ((← accountText (Lean.Json.mkObj [("status", Lean.Json.str "noAccount"), ("user", Lean.Json.null)])) == Real.CloudBackupError.unavailable.description)
  check "available: the user" ((← accountText (Lean.Json.mkObj [("status", Lean.Json.str "available"), ("user", Lean.Json.str "_u")])) == "ok")

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
  let listed ← (cloud.list "signet").toBaseIO
  check "list: this network's backups, newest first" (match listed with
    | .ok l => l.map (·.id) == #[b, a] && l.map (·.savedAt) == #[200, 100] | _ => false)
  check "list: the query names the record type, network and container" ((← asked.get).any fun (n, args) =>
    n == "cloudkit.query" && (args.getObjValAs? String "type").toOption == some "WalletBackup" &&
    (args.getObjValAs? String "container").toOption == some Real.cloudContainer && (args.getObjVal? "equals").toOption == some (obj [("network", "signet")]))
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("error", "tooLarge")]
  check "load: an asset over the limit is an invalid backup" (match ← (cloud.load a "_u").toBaseIO with
    | .error e => toString e == Real.CloudBackupError.invalidBackup.description | .ok _ => false)
  answer fun name _ => match name with
    | "cloudkit.account" => obj [("status", "available"), ("user", "_u")]
    | _ => obj [("error", "quotaExceeded"), ("code", (25 : Int)), ("detail", "iCloud storage is full")]
  check "load: another CloudKit error is its detail" (match ← (cloud.load a "_u").toBaseIO with
    | .error e => toString e == "iCloud storage is full" | .ok _ => false)
  -- the wrapping keys: synchronizable, 32 bytes
  let keys := Real.shellCloudKeys ask
  answer fun _ _ => obj [("hex", Lean.Json.null), ("status", (-25300 : Int))]
  check "keys: missing is keyUnavailable" (match ← (keys.load a).toBaseIO with
    | .error e => toString e == Real.CloudBackupError.keyUnavailable.description | .ok _ => false)
  check "keys: asked as a synchronizable item of this app's service" ((← asked.get).any fun (n, args) =>
    n == "keychain.get" && (args.getObjValAs? Bool "synchronizable").toOption == some true && (args.getObjValAs? String "service").toOption == some Real.cloudBackupKeyService)
  answer fun _ _ => obj [("hex", "0011"), ("status", (0 : Int))]
  check "keys: a key of the wrong size is an invalid backup" (match ← (keys.load a).toBaseIO with
    | .error e => toString e == Real.CloudBackupError.invalidBackup.description | .ok _ => false)

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
    let asked ← waitUntil 5000 prompted.isResolved
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
    check s!"{name} during the prompt: no failure is shown" ((← p.app.controller.get).message.isNone)
    p.backend.cloudScene false
    p.backend.stopNetworking

def main (args : List String) : IO UInt32 := do
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
  runTest "automaticCloud" (automaticCloudTests root)
  runTest "scopedPreparation" (scopedPreparationTests root)
  runTest "restoreFromICloud" (restoreFromICloud root)
  try IO.FS.removeDirAll root catch _ => pure ()
  let f ← failures.get
  IO.println s!"cloud-backup-test: {← passed.get} passed, {f.size} failed"
  return if f.isEmpty then 0 else 1
