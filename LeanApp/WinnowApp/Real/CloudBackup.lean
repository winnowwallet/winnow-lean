import WinnowApp.Real.CloudAppState
import WinnowApp.Real.Shell
import ElmLean.Native.Client.CloudKit
import ElmLean.Native.Client.Keychain
import WinnowApp.Real.Base

/-! # Automatic iCloud backup (`CloudBackupController.swift`, `ICloudBackupStore.swift`, upstream d2ca878)

The controller owns the backup's preferences, preparation, retries, account binding and the
successful-save state; it holds no secret beyond the encrypted copy it is updating. The store (CloudKit's
private database, one `WalletBackup` record per device's backup) and the wrapping keys (a synchronizable
iCloud Keychain service, separate from the wallet's own device-only key) come in as interfaces: on the
phone the shell's `cloudkit.*` and `keychain.*` capabilities (`shellCloudStore`, `shellCloudKeys`), in
tests memory versions.

Files, in the network's directory (excluded from backup): `cloud-backup.json`, the encrypted copy being
kept current (`{"walletID","account"?,"backup":{…},"digest":base64,"pendingUpload"?}`, as Swift's
`JSONEncoder` wrote it, so an installed Swift build's file reads here), and
`cloud-backup-preferences.json`, the sorted ids of the wallets whose automatic backup was turned off.

Cancellation (`CancellationError`, `check(token)`): every operation remembers the controller's
generation when it starts, and `suspend` (a closed presentation, the background, a wallet switch) ends it;
an operation whose generation ended changes nothing and fails with `cancelledText`. -/

namespace WinnowApp.Real
open Winnow SwiftJSON Lean

/-- `ICloudBackupSummary`. `savedAt` is seconds since 2001 (Foundation's reference date). -/
structure CloudBackupSummary where
  id : String
  network : String
  savedAt : Float
  deriving Inhabited, Repr, BEq

/-- `ICloudBackupError`. -/
inductive CloudBackupError where
  | unavailable | keyUnavailable | accountChanged | invalidBackup | unsupportedWallet
  /-- A build without the iCloud entitlement (the shell's `missingEntitlement`): the user may well be signed in. -/
  | missingEntitlement
  deriving BEq, Repr

def CloudBackupError.description : CloudBackupError → String
  | .unavailable => "Sign in to iCloud and enable iCloud Drive and Passwords & Keychain in Settings."
  | .keyUnavailable => "The backup key hasn’t arrived from iCloud Keychain. Check Passwords & Keychain in Settings and try again. Keep your recovery words and a backup file."
  | .accountChanged => "Your Apple Account changed. Sign back into the original account, or turn automatic backup off and on in Advanced to use this account."
  | .unsupportedWallet => "Automatic iCloud recovery requires this wallet’s recovery words. This wallet needs a backup file instead."
  | .invalidBackup => "This iCloud backup could not be read safely. Your existing wallet was not replaced."
  | .missingEntitlement => cloudMissingEntitlementText

def CloudBackupError.throw {α} (e : CloudBackupError) : IO α := failText e.description

/-- What a cancelled operation fails with (`CancellationError`); callers drop it quietly. -/
def cancelledText : String := "Winnow.CancellationError"
def throwCancelled {α} : IO α := failText cancelledText
def isCancellation (e : IO.Error) : Bool := toString e == cancelledText

/-- `ICloudBackupStoring`. -/
structure CloudBackupStore where
  account : IO String
  list : (network : String) → IO (Array CloudBackupSummary)
  save : CloudWalletBackup → (account : String) → IO Unit
  load : (id account : String) → IO CloudWalletBackup

/-- `ICloudBackupKeyStoring`: a random 256-bit wrapping key per backup id. -/
structure CloudBackupKeys where
  load : (id : String) → IO ByteArray
  create : (id : String) → IO ByteArray

/-- `Configuration`: the encrypted copy being kept current, and what was uploaded last. -/
structure CloudConfiguration where
  walletID : String
  account : Option String := none
  backup : CloudWalletBackup
  digest : ByteArray
  pendingUpload : Option Bool := none

namespace CloudConfiguration

def toJV (c : CloudConfiguration) : JV :=
  obj [("walletID", some (.str c.walletID)), ("account", c.account.map .str), ("backup", some c.backup.toJV),
       ("digest", some (ofData c.digest)), ("pendingUpload", c.pendingUpload.map .bool)]

def decode (data : ByteArray) : IO CloudConfiguration := do
  let some text := String.fromUTF8? data | CloudBackupError.invalidBackup.throw
  let fields := decodeText text fun v => do
    let kvs ← asObject v
    return (← key kvs "walletID" asString, ← keyIfPresent kvs "account" asString, ← key kvs "backup" pure,
            ← key kvs "digest" asData, ← keyIfPresent kvs "pendingUpload" asBool)
  let (walletID, account, backupJV, digest, pendingUpload) ← match fields with
    | .ok f => pure f
    | .error _ => CloudBackupError.invalidBackup.throw
  let backup ← runWM (CloudWalletBackup.decode (write backupJV).toUTF8)
  return { walletID, account, backup, digest, pendingUpload }

end CloudConfiguration

/-- `CloudBackupController`'s state (its stored properties). Times are seconds since 1970. -/
structure CloudControllerState where
  configuration : Option CloudConfiguration := none
  configurationPath : Option System.FilePath := none
  configuredWalletID : Option String := none
  preferencePath : Option System.FilePath := none
  disabledWallets : List String := []
  automaticEnabled : Bool := true
  retryAfter : Float := 0
  failureCount : Nat := 0
  /-- `task != nil`: a scheduled update is waiting or running. -/
  scheduled : Bool := false
  generation : Nat := 0
  busy : Bool := false
  message : Option String := none
  available : Array CloudBackupSummary := #[]

namespace CloudControllerState

def enabled (s : CloudControllerState) : Bool := s.configuration.isSome
def needsPreparation (s : CloudControllerState) : Bool := s.automaticEnabled && s.configuration.isNone

/-- `lastSaved`: the copy CloudKit last acknowledged (none while an upload is pending). -/
def lastSaved (s : CloudControllerState) : Option Float :=
  match s.configuration with
  | some c => if c.pendingUpload == some true then none else some c.backup.savedAt
  | none => none

def statusTitle (s : CloudControllerState) : String :=
  if !s.automaticEnabled || s.message.isSome then "Not backed up"
  else if s.busy || (s.configuration.bind (·.pendingUpload)) == some true then "Backing up"
  else if s.lastSaved.isNone then "Not backed up" else "Backed up"

end CloudControllerState

/-- `Date().timeIntervalSince1970`. -/
def unixNowFloat : IO Float := do
  let ns := (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val
  return Float.ofInt ns / 1e9

structure CloudBackupController where
  store : CloudBackupStore
  keys : CloudBackupKeys
  state : IO.Ref CloudControllerState
  /-- Called after every change the screens show (the controller is `@Observable`). -/
  observers : IO.Ref (Array (IO Unit))
  /-- How long a scheduled update waits first (5 s). -/
  scheduleDelayMs : Nat := 5_000
  now : IO Float := unixNowFloat

namespace CloudBackupController

def new (store : CloudBackupStore) (keys : CloudBackupKeys) (scheduleDelayMs : Nat := 5_000) : IO CloudBackupController := do
  return { store, keys, state := ← IO.mkRef {}, observers := ← IO.mkRef #[], scheduleDelayMs }

def get (c : CloudBackupController) : IO CloudControllerState := c.state.get

def changed (c : CloudBackupController) : IO Unit := do
  for o in ← c.observers.get do try o catch _ => pure ()

def modify (c : CloudBackupController) (f : CloudControllerState → CloudControllerState) : IO Unit := do
  c.state.modify f
  c.changed

def modifyGet {α} (c : CloudBackupController) (f : CloudControllerState → α × CloudControllerState) : IO α := do
  let a ← c.state.modifyGet f
  c.changed
  return a

/-- `suspend()`: the current operations' generation ends. -/
def suspend (c : CloudBackupController) : IO Unit :=
  c.modify fun s => { s with generation := s.generation + 1, scheduled := false, busy := false }

/-- `check(token)`. -/
def check (c : CloudBackupController) (token : Nat) : IO Unit := do
  if (← c.get).generation != token then throwCancelled

/-- `persist(_:to:)`: only encrypted wallet material; the folder is excluded from backup. -/
def persist (saved : CloudConfiguration) (path : System.FilePath) : IO Unit :=
  Winnow.IO.writeAtomic path (write saved.toJV).toUTF8

/-- `configure(directory:walletID:)`: the network's directory and the open wallet; unchanged, nothing happens. -/
def configure (c : CloudBackupController) (directory : Option System.FilePath) (walletID : Option String) : IO Unit := do
  let path := directory.map (· / "cloud-backup.json")
  let s ← c.get
  if path == s.configurationPath && walletID == s.configuredWalletID then return
  c.suspend
  let preferencePath := directory.map (· / "cloud-backup-preferences.json")
  let reset (s : CloudControllerState) : CloudControllerState :=
    { s with configurationPath := path, configuredWalletID := walletID, configuration := none, message := none,
             failureCount := 0, retryAfter := 0, preferencePath, disabledWallets := [], automaticEnabled := true }
  c.modify reset
  let mut disabled : List String := []
  if let some p := preferencePath then
    if ← p.pathExists then
      let read : IO (List String) := do
        let some text := String.fromUTF8? (← IO.FS.readBinFile p) | throw (IO.userError "")
        match decodeText text (asArray asString) with
        | .ok ids => pure ids.toList
        | .error e => throw (IO.userError e)
      match ← read.toBaseIO with
      | .ok ids => disabled := ids
      | .error _ =>
        let unreadable := "Backup preferences couldn’t be read. Review automatic backup in Advanced settings."
        c.modify fun s => { s with automaticEnabled := false, message := some unreadable }
        return
  let automatic := !disabled.contains (walletID.getD "")
  c.modify fun s => { s with disabledWallets := disabled, automaticEnabled := automatic }
  let (true, some p, some w) := (automatic, path, walletID) | return
  if !(← p.pathExists) then return
  let loaded : IO CloudConfiguration := do
    let data ← IO.FS.readBinFile p
    unless data.size ≤ CloudWalletBackup.maximumBytes + 4096 do CloudBackupError.invalidBackup.throw
    CloudConfiguration.decode data
  match ← loaded.toBaseIO with
  | .ok saved => if saved.walletID == w then c.modify fun s => { s with configuration := some saved }
  | .error _ =>
    let unreadable := "Automatic backup settings couldn’t be read. Your previous iCloud backup is unchanged."
    c.modify fun s => { s with message := some unreadable }

/-- `setAutomatic(_:)`: the preference for the configured wallet; turning it off keeps the iCloud copies. -/
def setAutomatic (c : CloudBackupController) (enabled : Bool) : IO Unit := do
  let s ← c.get
  let (some walletID, some prefs) := (s.configuredWalletID, s.preferencePath) | CloudBackupError.unavailable.throw
  let updated := if enabled then s.disabledWallets.erase walletID
    else if s.disabledWallets.contains walletID then s.disabledWallets else s.disabledWallets ++ [walletID]
  let sorted := (updated.toArray.qsort (· < ·)).toList
  Winnow.IO.writeAtomic prefs (write (.arr (sorted.toArray.map JV.str))).toUTF8
  c.modify fun s => { s with disabledWallets := updated, automaticEnabled := enabled }
  c.suspend
  let message := if enabled then none else some "Automatic backup is off. Existing iCloud copies remain available."
  c.modify fun s =>
    { s with retryAfter := 0, failureCount := 0, message, configuration := if enabled then s.configuration else none }
  if !enabled then
    if let some p := s.configurationPath then
      if ← p.pathExists then IO.FS.removeFile p

def accountForPreparation (c : CloudBackupController) : IO String := c.store.account

def reportPreparationFailure (c : CloudBackupController) (e : IO.Error) : IO Unit :=
  -- the status already says "Not backed up": the message is the reason alone
  c.modify fun s => { s with message := some (toString e) }

def reportResumeFailure (c : CloudBackupController) (e : IO.Error) : IO Unit :=
  c.modify fun s => { s with message := some s!"Wallet restored. Automatic backup needs attention: {e}" }

/-- `prepare(contents:walletID:account:)`: a new backup id and wrapping key, the encrypted copy written
locally before any upload (so an outage does not silently turn backups off). -/
def prepare (c : CloudBackupController) (contents : CloudBackupContents) (walletID : String) (account : Option String := none) :
    IO Unit := do
  let s ← c.get
  if !s.automaticEnabled then return
  let some path := s.configurationPath | CloudBackupError.unavailable.throw
  if s.busy || s.configuredWalletID != some walletID then CloudBackupError.unavailable.throw
  let id ← UUIDText.random
  let key ← c.keys.create id
  let backup ← runWM (CloudWalletBackup.create contents.bundle key contents.appState (some id))
  let saved : CloudConfiguration := { walletID, account, backup, digest := contents.digest, pendingUpload := some true }
  persist saved path
  c.modify fun s => { s with configuration := some saved, message := none }

/-- `update(token:export:)`: when the contents changed (or the first upload is pending), re-seal the wallet
box under the copy's key and save it to the account the copy is bound to (the first available account is
pinned before the first upload). -/
def updateWith (c : CloudBackupController) (token : Nat) (export_ : IO CloudBackupContents) : IO Unit := do
  let s ← c.get
  let (true, some saved, some path) := (s.automaticEnabled, s.configuration, s.configurationPath) | return
  let contents ← export_
  c.check token
  let digest := contents.digest
  if digest == saved.digest && saved.pendingUpload != some true then
    c.modify fun s => { s with message := none }
    return
  c.modify fun s => { s with busy := true }
  try
    let key ← c.keys.load saved.backup.id
    let backup ← runWM (saved.backup.updating contents.bundle key contents.appState)
    let mut saved := saved
    if saved.account.isNone then
      saved := { saved with account := some (← c.store.account) }
      c.check token
      persist saved path
      let pinned := saved
      c.modify fun s => { s with configuration := some pinned }
    let some account := saved.account | CloudBackupError.unavailable.throw
    c.store.save backup account
    c.check token
    let done := { saved with backup, digest, pendingUpload := some false }
    persist done path
    c.modify fun s => { s with configuration := some done, failureCount := 0, retryAfter := 0, message := none }
  finally
    c.modify fun s => if s.generation == token then { s with busy := false } else s

def update (c : CloudBackupController) (export_ : IO CloudBackupContents) : IO Unit := do
  c.updateWith (← c.get).generation export_

/-- `enable(bundle:appState:walletID:)`: the explicit retry in Advanced settings. -/
def enable (c : CloudBackupController) (bundle : ImportBundle) (appState : Option ByteArray := none) (walletID : String) : IO Unit := do
  c.setAutomatic true
  let contents : CloudBackupContents := { bundle, appState }
  c.prepare contents walletID
  c.update (pure contents)

/-- `schedule(export:)`: unless turned off, after 5 s, one update; a failure backs off from 60 s up to five
minutes. No secret is read and no authentication asked: the first encrypted phrase is carried forward. -/
def schedule (c : CloudBackupController) (export_ : IO CloudBackupContents) : IO Unit := do
  let now ← c.now
  let claim ← c.modifyGet fun s =>
    if !s.automaticEnabled || s.configuration.isNone || s.scheduled || s.busy || now < s.retryAfter then (none, s)
    else (some s.generation, { s with scheduled := true })
  let some token := claim | return
  discard <| IO.asTask (prio := .dedicated) do
    try
      -- `Task.sleep(for: .seconds(5))`, cancelled by a suspend
      let deadline := (← IO.monoMsNow) + c.scheduleDelayMs
      while (← IO.monoMsNow) < deadline do
        if (← c.get).generation != token then throwCancelled
        IO.sleep 50
      c.updateWith token export_
    catch e =>
      if !isCancellation e && (← c.get).generation == token then
        let now ← c.now
        c.modify fun s =>
          let failures := s.failureCount + 1
          let delay := min 300 (30 * (2 : Float) ^ (min failures 4).toFloat)
          { s with message := some s!"Backup needs attention: {e}", failureCount := failures, retryAfter := now + delay }
    c.modify fun s => if s.generation == token then { s with scheduled := false } else s

/-- `discover(network:)`: the saved backups for this network, newest first. -/
def discover (c : CloudBackupController) (network : String) : IO Unit := do
  let claim ← c.modifyGet fun s =>
    if s.busy then (none, s) else (some s.generation, { s with busy := true, message := none, available := #[] })
  let some token := claim | return
  try
    let found ← c.store.list network
    c.check token
    c.modify fun s => { s with available := found }
  catch e =>
    if !isCancellation e && (← c.get).generation == token then c.modify fun s => { s with message := some (toString e) }
  finally
    c.modify fun s => if s.generation == token then { s with busy := false } else s

/-- `Restoration`: what a backup restores, and the account it came from. -/
structure Restoration where
  contents : CloudBackupContents
  account : String

/-- `restoreContents(_:)` (the caller has authenticated): the backup downloaded and opened with its key. -/
def restoreContents (c : CloudBackupController) (id : String) : IO Restoration := do
  let token := (← c.get).generation
  let account ← c.store.account
  let backup ← c.store.load id account
  c.check token
  let key ← c.keys.load id
  let bundle ← runWM (backup.restoredBundle key)
  let appState ← runWM (backup.restoredAppState key)
  return { contents := { bundle, appState }, account }

def restore (c : CloudBackupController) (id : String) : IO ImportBundle := do
  return (← c.restoreContents id).contents.bundle

/-- `resume(contents:walletID:account:)`: a replacement device gets its own record, bound to the account
it restored from. -/
def resume (c : CloudBackupController) (contents : CloudBackupContents) (walletID account : String) : IO Unit :=
  c.prepare contents walletID (some account)

def stop (c : CloudBackupController) : IO Unit := c.setAutomatic false

end CloudBackupController

/-! ## Dates as the screens show them -/

/-- `Date.formatted()` in the phone's time zone (en_US: "10/27/2026, 7:28 PM"); UTC when the zone cannot
be read. `savedAt` is seconds since 2001. -/
def formatReferenceDate (savedAt : Float) : IO String := do
  let unix := (savedAt + 978_307_200).floor
  let ts := Std.Time.Timestamp.ofSecondsSinceUnixEpoch ⟨Int.ofNat unix.toUInt64.toNat⟩
  let rules ← try Std.Time.Database.defaultGetLocalZoneRules catch _ => pure (Std.Time.TimeZone.ZoneRules.ofTimeZone Std.Time.TimeZone.UTC)
  let dt := Std.Time.DateTime.ofTimestamp ts rules
  let hour := dt.hour.val.toNat
  let h12 := if hour % 12 == 0 then 12 else hour % 12
  let minute := dt.minute.val.toNat
  return s!"{dt.month.val}/{dt.day.val}/{dt.year}, {h12}:{if minute < 10 then "0" else ""}{minute} {if hour < 12 then "AM" else "PM"}"

/-! ## The shell's CloudKit and iCloud Keychain (`ICloudBackupStore`, `ICloudBackupKeys`) -/

def cloudContainer : String := "iCloud.com.btcswift.app"
def cloudBackupKeyService : String := "com.btcswift.app.cloud-backup-key.v1"
def cloudRecordType : String := "WalletBackup"

open ElmLean.Native in
/-- A CloudKit failure as the text the screens show (`missingEntitlement` and `notAuthenticated` as Swift's
errors, anything else as the shell's detail or name). -/
def cloudErrorText (e : Client.Error) : String :=
  match e.name with
  | "missingEntitlement" => CloudBackupError.missingEntitlement.description
  | "notAuthenticated" => CloudBackupError.unavailable.description
  | name => if e.detail.isEmpty then name else e.detail

open ElmLean.Native in
/-- One record per device's backup, in the private database; never the public one. Through
`Client.CloudKit`, with this app's container, record type and fields. -/
def shellCloudStore (ask : Ask) : CloudBackupStore :=
  let container := some cloudContainer
  let call {α} (r : Client.Request α) : IO (Client.Result α) := callAsk ask r
  let account : IO String := do
    match ← call (Client.CloudKit.account container) with
    -- a build without the entitlement answers an error, not a status: say which
    | .error e => failText (cloudErrorText e)
    | .ok { status := .available, user := some user } => pure user
    | .ok _ => CloudBackupError.unavailable.throw
  { account
    list := fun network => do
      discard account
      let query : Client.CloudKit.Query :=
        { type := cloudRecordType
          equals := [("network", Client.CloudKit.Field.str network)]
          sortBy := some "savedAt"
          ascending := false
          keys := some ["network", "savedAt"]
          limit := some 500
          container := container }
      let q ← call (Client.CloudKit.query query)
      let records ← match q with
        | .ok r => pure r.records
        | .error e => failText (cloudErrorText e)
      let found := records.filterMap fun record => do
        let sameNetwork : Bool := match record.field? "network" with | some (.str n) => n == network | _ => false
        guard sameNetwork
        let id ← UUIDText.canonical? record.name
        let date ← match record.field? "savedAt" with | some (.date d) => some d | _ => none
        return ({ id, network, savedAt := date - 978_307_200 } : CloudBackupSummary)
      return found.qsort (·.savedAt > ·.savedAt)
    save := fun backup expected => do
      unless (← account) == expected do CloudBackupError.accountChanged.throw
      let data ← runWM backup.encoded
      let record : Client.CloudKit.Save :=
        { type := cloudRecordType
          name := backup.id
          fields := [("network", .str backup.network), ("savedAt", .date (backup.savedAt + 978_307_200))]
          asset := some data
          assetField := some "payload"
          container := container }
      match ← call (Client.CloudKit.save record) with
      | .ok _ => pure ()
      | .error e => if e.kind == .malformed then CloudBackupError.invalidBackup.throw else failText (cloudErrorText e)
      unless (← account) == expected do CloudBackupError.accountChanged.throw
    load := fun id expected => do
      unless (← account) == expected do CloudBackupError.accountChanged.throw
      let loaded ← call (Client.CloudKit.load id (maxBytes := some CloudWalletBackup.maximumBytes)
        (assetField := some "payload") (container := container))
      let data ← match loaded with
        | .ok (_, some data) => pure data
        | .ok (_, none) => CloudBackupError.invalidBackup.throw
        | .error e =>
          if e.name == "tooLarge" || e.kind == .malformed then CloudBackupError.invalidBackup.throw
          else failText (cloudErrorText e)
      unless data.size ≤ CloudWalletBackup.maximumBytes do CloudBackupError.invalidBackup.throw
      let backup ← runWM (CloudWalletBackup.decode data)
      unless backup.id == id && (← account) == expected do CloudBackupError.accountChanged.throw
      return backup }

open ElmLean.Native in
/-- The wrapping keys: a synchronizable iCloud Keychain item per backup id (raw 32 bytes), kept apart from
the wallet's device-only key so automatic recovery never changes its protection. -/
def shellCloudKeys (ask : Ask) : CloudBackupKeys :=
  let item (id : String) : Client.Keychain.Item := { key := id, service := some cloudBackupKeyService, synchronizable := true }
  { load := fun id => do
      match ← (callAsk ask (Client.Keychain.get (item id)) : IO _) with
      | .ok (some k) => if k.size == 32 then pure k else CloudBackupError.invalidBackup.throw
      | .ok none => CloudBackupError.keyUnavailable.throw
      | .error e => if e.kind == .malformed then CloudBackupError.invalidBackup.throw else CloudBackupError.keyUnavailable.throw
    create := fun id => do
      let key ← IO.getRandomBytes 32
      match ← (callAsk ask (Client.Keychain.set (item id) key) : IO _) with
      | .ok () => return key
      | .error e => failText (keyStoreErrorText (keychainError e)) }

/-- Memory versions for tests (`MemoryCloudBackups`, `MemoryCloudKeys`). -/
structure MemoryCloud where
  records : IO.Ref (Array CloudWalletBackup)
  failing : IO.Ref Bool
  accountName : IO.Ref String
  accountUnavailable : IO.Ref Bool
  saveAttempts : IO.Ref Nat
  saves : IO.Ref Nat
  /-- `holdNextSave`: the next save waits for this promise after it stored the record. -/
  hold : IO.Ref (Option (IO.Promise Unit))
  holding : IO.Ref Bool

namespace MemoryCloud

def new : IO MemoryCloud := do
  return { records := ← IO.mkRef #[], failing := ← IO.mkRef false, accountName := ← IO.mkRef "first-account",
           accountUnavailable := ← IO.mkRef false, saveAttempts := ← IO.mkRef 0, saves := ← IO.mkRef 0,
           hold := ← IO.mkRef none, holding := ← IO.mkRef false }

def store (m : MemoryCloud) : CloudBackupStore where
  account := do
    if ← m.accountUnavailable.get then CloudBackupError.unavailable.throw
    m.accountName.get
  list := fun network => do
    return (← m.records.get).filter (·.network == network) |>.map fun b => { id := b.id, network := b.network, savedAt := b.savedAt }
  save := fun backup account => do
    m.saveAttempts.modify (· + 1)
    unless account == (← m.accountName.get) do CloudBackupError.accountChanged.throw
    if ← m.failing.get then CloudBackupError.unavailable.throw
    m.records.modify fun rs => (rs.filter (·.id != backup.id)).push backup
    m.saves.modify (· + 1)
    if let some gate ← m.hold.get then
      m.hold.set none
      m.holding.set true
      discard <| IO.wait gate.result?
  load := fun id _ => do
    match (← m.records.get).find? (·.id == id) with
    | some b => pure b
    | none => CloudBackupError.invalidBackup.throw

def count (m : MemoryCloud) : IO Nat := return (← m.records.get).size

end MemoryCloud

def memoryCloudKeys : IO CloudBackupKeys := do
  let keys ← IO.mkRef (#[] : Array (String × ByteArray))
  return {
    create := fun id => do
      let k ← IO.getRandomBytes 32
      keys.modify (·.push (id, k))
      return k
    load := fun id => do
      match (← keys.get).find? (·.1 == id) with
      | some (_, k) => pure k
      | none => CloudBackupError.keyUnavailable.throw }

end WinnowApp.Real
