import WinnowApp.Real.Full
import WinnowApp.Real.CloudBackup
import WinnowApp.Real.DeviceSync
import LeanNative.Native.EffectScope

/-! # AppModel's iCloud backup (the `AppModel` extension in AppModel.swift, upstream d2ca878 :3485–3651)

Automatic backup runs unless turned off, in every part of the app, and never decides whether the
wallet can be used:

* **Creation and import** stage only ciphertext while the creation's authentication is valid
  (`prepareCloudBackup`), from the recovery words in hand; network availability never decides whether
  onboarding finishes.
* **An existing wallet** without a backup is prepared at a foreground opportunity, at most once per
  foreground session per wallet (`scheduleAutomaticCloudPreparation`): the account first, with no prompt
  (an unavailable Apple Account never asks for authentication), then device authentication, the words,
  the copy.
* **Updates** (`scheduleCloudBackup`) export fresh public wallet state and the app context after a refresh,
  without reading the signing key again: the first encrypted phrase is carried forward.
* **Restore** (`restoreCloudBackup`) authenticates, downloads and opens the backup, plans the people and
  signer merges, imports the bundle and, inside the import's commit, applies the context and starts this
  device's own backup record bound to the same account.

* **The person's other devices** (`SyncApp`, `Real/DeviceSync.lean`): every backup says when each of its
  accounts and signers last changed (`cloudAppState`'s `sync`), and while the scene is active a loop of its
  own looks, when a look is due, at the other devices' backups and takes what they have that this device
  lacks (`tick` and `sceneChanged` begin it, the background ends it).

Test mode never uses iCloud (`allowsCloudBackup`). The context's display name is the Model's setting here: a
restore hands it back (`CloudRestored.context`) for the Model to save. The context's Advanced switch stays in
the format (shared with the Swift app); this app has one mode, writes it on and applies nothing from it. -/

namespace WinnowApp
open Winnow Winnow.IO

namespace Real
open RecordsReal

/-- What the app's iCloud flows hold beside the controller (AppModel's cloud properties). -/
structure CloudApp where
  controller : CloudBackupController
  env : Env
  host : RecordsHost
  multisig : MultisigApp
  /-- Keeping accounts and signers in step with the person's other devices. -/
  follow : SyncApp
  /-- `allowsCloudBackup`: never in test mode. -/
  allows : Bool
  /-- `authenticateSensitiveAction(reason:)`: device-owner authentication (throws when declined). -/
  authenticate : String → IO Unit
  /-- `attemptedCloudPreparation`: the wallets prepared (or tried) this foreground session. -/
  attempted : IO.Ref (List String)
  /-- `cloudPreparationTask != nil`: the running preparation's token. -/
  preparing : IO.Ref (Option LeanNative.Native.EffectScope.Token)
  /-- `cloudPreparationEpoch`, as LeanNative's `EffectScope`: a new preparation, the background and a wallet
  change end it, and the protected part (the words, the copy) runs as its task. -/
  preparation : LeanNative.Native.EffectScope
  /-- `cloudPreparationTask`: the last preparation's task, which ends after its scope's checks. -/
  preparationTask : IO.Ref (Option (Task (Except IO.Error Unit)))
  /-- `cloudRestoreNotice`. -/
  restoreNotice : IO.Ref (Option String)
  /-- Whether the scene is active (`isActive`), as the cloud flows last heard. -/
  wasActive : IO.Ref Bool
  /-- The scene went to the background and has not come back: the iCloud work it suspended stays suspended. Not
  `!wasActive`, which is also what a launch straight into the foreground looks like (no scene change comes). -/
  inBackground : IO.Ref Bool
  /-- Which wallet each saved backup is of, as far as this device could read (by backup id and save date). -/
  labels : IO.Ref (Array (String × Float × Option String))

namespace CloudApp

def new (controller : CloudBackupController) (env : Env) (host : RecordsHost) (multisig : MultisigApp) (follow : SyncApp)
    (allows : Bool) (authenticate : String → IO Unit) : IO CloudApp := do
  return { controller, env, host, multisig, follow, allows, authenticate, attempted := ← IO.mkRef [], preparing := ← IO.mkRef none,
           preparation := ← LeanNative.Native.EffectScope.new, preparationTask := ← IO.mkRef none, restoreNotice := ← IO.mkRef none, wasActive := ← IO.mkRef false, inBackground := ← IO.mkRef false, labels := ← IO.mkRef #[] }

def directory (a : CloudApp) : IO (Option System.FilePath) := do return (← a.env.get).dir.map System.FilePath.mk
def walletID (a : CloudApp) : IO (Option String) := do return (← a.env.get).wallet.map (·.id)
def network (a : CloudApp) : IO (Option WinnowApp.Network) := do return (← a.env.get).network

/-- `cloudBackups.configure(directory: storageDirectory(), walletID: walletID)`. -/
def configureCurrent (a : CloudApp) : IO Unit := do
  a.controller.configure (← a.directory) (← a.walletID)

/-- At most this many of the newest saved backups are opened to say which wallet each is of. -/
def maximumLabelled : Nat := 30

/-- Says which wallet each backup found is of: its wallet box read for its descriptor alone, with its key from
iCloud Keychain (never the words' box). A person with several wallets, or several devices, otherwise chooses
among dates. One whose key has not arrived, or that does not open, stays unnamed and is tried again at the
next search. -/
def labelBackups (a : CloudApp) : IO Unit := do
  let found := (← a.controller.get).available
  let known := (← a.labels.get).filter fun (id, savedAt, _) => found.any fun b => b.id == id && b.savedAt == savedAt
  let mut labels := known.filter (·.2.2.isSome)
  let account ← match ← a.controller.store.account.run with
    | .ok account => pure account
    | .error _ => a.labels.set labels; return
  for b in found.extract 0 maximumLabelled do
    if labels.any fun (id, savedAt, _) => id == b.id && savedAt == b.savedAt then continue
    let read : CloudM (Option String) := do
      let key ← a.controller.keys.load b.id
      let backup ← a.controller.store.load b.id account
      return (← CloudM.liftWM (backup.shared key)).walletID
    match ← read.run with
    | .ok (some wallet) => labels := labels.push (b.id, b.savedAt, some wallet)
    | _ => pure ()
  a.labels.set labels

/-- `discoverCloudBackups()`: onboarding's search for this network's saved backups. -/
def discover (a : CloudApp) : IO Unit := do
  if !a.allows || (← a.walletID).isSome then return
  let some n ← a.network | return
  -- the backup is pointed at this place before the search: the app's tick points it there too, and doing so
  -- during the search ended the search (its generation), with nothing offered and nothing said
  a.configureCurrent
  for _ in [0:3] do
    -- an update still running for the wallet that was open keeps the controller busy, and a search then does
    -- nothing: it is waited for, a few seconds at most
    for _ in [0:20] do
      unless (← a.controller.get).busy do break
      IO.sleep 250
    let before := (← a.controller.get).generation
    a.controller.discover n.name
    -- a search that ran to its end, found something or not, is the answer; one cut short is made again
    if (← a.controller.get).generation == before || (← a.walletID).isSome then break
    a.configureCurrent
  a.labelBackups
  -- which wallet each backup is of is not the controller's state: the screens are told again
  a.controller.changed


/-- `cloudAppState(for:)`: people, receive-address labels, the display name and the Advanced switch,
validated against the bundle. -/
def cloudAppState (a : CloudApp) (bundle : ImportBundle) : IO CloudAppState := do
  let some walletID ← a.walletID | failWith .noWallet
  let store ← a.host.store
  let st ← store.read
  let labels ← store.labelStore st walletID
  let settings := ((← a.env.get).settings).getD {}
  let sync ← if a.allows then a.follow.publish else pure none
  let named ← match (← a.env.get).dir with
    | some dir => readProfileName dir
    | none => pure none
  let state : CloudAppState := {
    network := bundle.network, descriptor := bundle.descriptor, people := ← RM.toIO st.people.backup,
    receiveLabels := ← RM.toIO labels.backup, ownDisplayName := settings.ownDisplayName,
    -- the format (shared with the Swift app) keeps its Advanced switch: this app's one mode has every
    -- feature Advanced had, so a backup says it is on
    advancedMode := true,
    -- when each account and signer of this bundle last changed, for the person's other devices
    sync,
    profileName := named.map (·.1), profileNameStamp := named.map (·.2) }
  RM.toIO (state.validate bundle)
  return state

/-- The bundle as `exportWalletBundle(includeMnemonic: false)` writes it (the journal records the export). -/
def exportedBundle (a : CloudApp) : IO ImportBundle := do
  let json ← exportBundle a.env false
  match ImportBundle.decode json with
  | .ok b => pure b
  | .error e => failText (importFailureText e)

/-- `cloudContents(words:walletID:)`: the public bundle with the words put back, and the context; dropped
when the wallet or network changed meanwhile. -/
def cloudContents (a : CloudApp) (words walletID : String) : CloudM CloudBackupContents := do
  let network ← a.network
  let bundle := { (← a.exportedBundle) with mnemonic := some words }
  let state ← a.cloudAppState bundle
  unless (← a.walletID) == some walletID && (← a.network) == network do throw .cancelled
  return { bundle, appState := some state.encoded }

/-- `scheduleCloudBackup()`: after a refresh, while active, for the open wallet. -/
def scheduleBackup (a : CloudApp) : IO Unit := do
  if !a.allows then return
  a.configureCurrent
  let c ← a.env.get
  let (true, some w, network) := (c.active, c.wallet, c.network) | return
  a.controller.schedule do
    unless (← a.walletID) == some w.id && (← a.network) == network do throw .cancelled
    let bundle ← a.exportedBundle
    let state ← a.cloudAppState bundle
    unless (← a.walletID) == some w.id && (← a.network) == network do throw .cancelled
    return { bundle, appState := some state.encoded }

/-- `prepareCloudBackup(words:account:)`: stage the encrypted copy (only ciphertext) while the
authentication that read the words is valid. Never fails the caller. -/
def prepare (a : CloudApp) (words : String) (account : Option String := none) : IO Unit := do
  if !a.allows then return
  let some walletID ← a.walletID | return
  a.attempted.modify fun l => if l.contains walletID then l else l ++ [walletID]
  a.configureCurrent
  if !(← a.controller.get).needsPreparation then return
  let run : CloudM Unit := do
    let contents ← a.cloudContents words walletID
    a.controller.prepare contents walletID account
    a.scheduleBackup
  match ← run.run with
  | .ok () => pure ()
  | .error e => a.controller.reportFailure e

/-- `acceptsCloudPreparation(_:network:)`. -/
def accepts (a : CloudApp) (walletID : String) (network : Option WinnowApp.Network) : IO Bool := do
  let c ← a.env.get
  return c.wallet.map (·.id) == some walletID && c.network == network && c.active &&
    (← a.controller.get).needsPreparation

/-- `cloudRecoveryWords(walletID:)`: automatic recovery needs the words; an xprv-only or missing secret is
`unsupportedWallet`. -/
def recoveryWords (a : CloudApp) (walletID : String) : CloudM String := do
  match ← (a.env.deps.keyStore.load walletID).run with
  | .ok (.mnemonic words) => return words
  | .ok _ | .error (.notFound _) => CloudM.throwIssue .unsupportedWallet
  | .error _ => CloudM.throwIssue .keychainUnavailable

/-- `prepareExistingCloudBackup(walletID:network:)`: the account first (no prompt when iCloud is
unavailable), then authentication, the words, the copy. The preparation's scope is checked before the
prompt, and the words and the copy start only as the scope's task after the answer, so a wallet switch, a
network switch or the background while the person answers ends it before the protected part starts; this
app's own conditions (the same wallet, network, an active scene) are checked with it. Declined, nothing is
prepared (cloud-backup-test's `declinedDeviceCheck`, over the app's `authenticateNow`). -/
def prepareExisting (a : CloudApp) (walletID : String) (network : Option WinnowApp.Network)
    (token : LeanNative.Native.EffectScope.Token) : IO Unit := do
  let live : IO Bool := do return (← a.preparation.isValid token) && (← a.accepts walletID network)
  let authenticate : IO (LeanNative.Native.Client.Result Unit) := do
    try a.authenticate "Protect your wallet with automatic iCloud backup"; return .ok ()
    catch e => return .error { kind := .failed, name := "authentication", detail := toString e }
  let account ← match ← a.controller.accountForPreparation.run with
    | .ok acc => pure acc
    | .error e =>
      if ← live then a.controller.reportFailure e
      return
  if !(← live) then return
  let prepError ← IO.mkRef (none : Option CloudError)
  let r ← a.preparation.authenticated token authenticate do
    unless ← a.accepts walletID network do return
    match ← (a.recoveryWords walletID).run with
    | .ok words => a.prepare words (some account)
    | .error e => prepError.set (some e)
  match r with
  | .done () =>
    if let some e ← prepError.get then
      if ← live then a.controller.reportFailure e
  | .stale _ => pure ()
  | .failed e =>
    if ← live then a.controller.reportFailure (.failed (toString e))
  | .denied _ | .cancelled _ | .error _ =>
    if ← live then a.controller.reportFailure (.issue .authenticationRequired)

/-- `scheduleAutomaticCloudPreparation()`: a ready wallet with no backup, once per foreground session. -/
def schedulePreparation (a : CloudApp) : IO Unit := do
  if !a.allows then return
  let c ← a.env.get
  let (true, some w) := (c.active, c.wallet) | return
  if (← a.preparing.get).isSome then return
  a.configureCurrent
  if !(← a.controller.get).needsPreparation || (← a.attempted.get).contains w.id then return
  a.attempted.modify (· ++ [w.id])
  -- a new preparation ends any earlier one's scope
  discard <| a.preparation.invalidateWithoutWaiting
  let token ← a.preparation.capture
  a.preparing.set (some token)
  let network := c.network
  let task ← IO.asTask (prio := .dedicated) do
    a.prepareExisting w.id network token
    if ← a.preparation.isValid token then a.preparing.set none
  a.preparationTask.set (some task)

/-- What `refresh()` asks of the iCloud side: an update of the copy, a preparation if one is due, and that the
other devices' backups are being looked at (a launch straight into the foreground brings no scene change). -/
def tick (a : CloudApp) : IO Unit := do
  -- a sync iOS lets run on in the background (a continued sync) still reports its snapshots, and each asks
  -- this: none of them is a reason to start again what leaving the app suspended
  if ← a.inBackground.get then return
  a.scheduleBackup
  a.schedulePreparation
  a.follow.ensureRunning

/-- `scenePhaseChanged`: a new foreground session may prepare again; the background cancels preparation
and suspends the controller. -/
def sceneChanged (a : CloudApp) (active : Bool) : IO Unit := do
  let was ← a.wasActive.modifyGet fun w => (w, active)
  a.inBackground.set !active
  if active then
    if !was then
      a.attempted.set []
      -- back in the foreground: the other devices' backups are looked at now, and then while it stays open
      a.follow.lastRound.set none
      a.follow.start
  else
    a.follow.stop
    discard <| a.preparation.invalidateWithoutWaiting
    a.preparing.set none
    a.controller.suspend

/-- The wallet changed or went (`adopt`, `destroyWallet`, `switchNetwork`). -/
def walletChanged (a : CloudApp) : IO Unit := do
  -- without waiting: this hook can run inside the preparation's own task (the copy adopts the wallet)
  discard <| a.preparation.invalidateWithoutWaiting
  a.preparing.set none
  a.controller.configure none none
  a.follow.reset

/-- `setAutomaticCloudBackup(_:)` (Settings → Backup → iCloud backup). -/
def setAutomatic (a : CloudApp) (enabled : Bool) : IO Unit := do
  let some walletID ← a.walletID | return
  a.configureCurrent
  match ← (a.controller.setAutomatic enabled).run with
  | .ok () =>
    if enabled then
      a.attempted.modify (·.erase walletID)
      a.schedulePreparation
      a.scheduleBackup
  | .error e => a.controller.reportFailure e

/-- `applyCloudAppState(_:)`: people, signers and labels restored; the display name and Advanced switch
handed back to the Model (which saves the name only). -/
def applyAppState (a : CloudApp) (state : CloudAppState) : IO Unit := do
  let store ← a.host.store
  RM.toIO (store.modify fun st => do
    return ({ st with people := ← st.people.restore store.keys store.writeData state.people }, ()))
  if let some signers := state.signers then
    RM.toIO (a.multisig.signers.modify fun s => do return (← s.restore a.multisig.signers.keys a.multisig.signers.writeData signers, ()))
  let some walletID ← a.walletID | failWith .noWallet
  let st ← store.read
  let labels ← store.labelStore st walletID
  let restored ← RM.toIO (labels.restore store.writeData state.receiveLabels)
  RM.toIO (store.modify fun st => return ({ st with labels := some restored }, ()))
  -- the name it was given on the device the backup came from
  if let (some name, some dir) := (state.profileName, (← a.env.get).dir) then
    try writeProfileName dir name (state.profileNameStamp.getD 0) catch _ => pure ()

end CloudApp

/-- A restore's outcome as CloudRestoreView reads it. -/
structure CloudRestored where
  walletID : String
  /-- `ImportReport.matchesBundle`, or none while no peer was reachable for verification. -/
  matchesBundle : Option Bool
  /-- The restored context's display name and Advanced switch (none for an older backup without one). -/
  context : Option (String × Bool)

namespace CloudApp

/-- `restoreCloudBackup(_:)` (after authentication here): only onto a network with no wallet; nothing
replaces a wallet already on this phone. A declined check stops it before anything is written
(cloud-backup-test's `declinedDeviceCheck`; restored end to end in `restoreFromICloud`). -/
def restore (a : CloudApp) (n : WinnowApp.Network) (dir id : String) : CloudM CloudRestored := do
  if (← a.walletID).isSome || !a.allows then throw (.failed AppError.noWallet.text)
  a.restoreNotice.set none
  a.authenticate "Restore your wallet and signing key from iCloud"
  let restoration ← a.controller.restoreContents id
  let bundle := restoration.contents.bundle
  let mut appState ← CloudM.io (RM.toIO (CloudAppState.decode restoration.contents.appState bundle))
  if let some saved := appState then
    let store ← a.host.store
    let people ← CloudM.io (RM.toIO ((← store.read).people.planRestore saved.people))
    let signers ← CloudM.io (RM.toIO ((← a.multisig.signers.read).planRestore (saved.signers.getD #[])))
    appState := some { saved with people, signers := some signers }
  unless (← a.walletID).isNone && (← a.network) == some n do throw .cancelled
  let validated := appState
  let cancelled ← IO.mkRef false
  let (walletID, report) ← CloudM.io (importDecoded a.env n dir bundle fun restoredID => do
    unless (← a.walletID) == some restoredID && (← a.network) == some n do
      cancelled.set true
      return
    match validated with
    | some state => a.applyAppState state
    | none => a.restoreNotice.set (some "This older backup restores your wallet and key, but does not contain saved people or address labels.")
    a.configureCurrent
    let resume : CloudM Unit := do
      let current ← a.cloudAppState bundle
      a.controller.resume { bundle, appState := some current.encoded } restoredID restoration.account
    match ← resume.run with
    | .ok () => pure ()
    | .error e => a.controller.reportFailure e)
  if ← cancelled.get then throw .cancelled
  return { walletID, matchesBundle := report.map (·.matchesBundle),
           context := validated.map fun s => (s.ownDisplayName, s.advancedMode) }


/-- What Settings → Backup → iCloud backup says of the other devices after a round: when, how many of the
other backups were read, and of each that was not, when it was saved and why. -/
def devicesText (f : SyncStatus) (ago : String) : IO String := do
  let saved (why : Unread) : IO (List String) :=
    ((f.unread.filter (·.2 == why)).toList.take 3).mapM (formatReferenceDate ·.1)
  let count (why : Unread) : Nat := (f.unread.filter (·.2 == why)).size
  let backups (n : Nat) : String := if n == 1 then "1 backup" else s!"{n} backups"
  let dates (ds : List String) (n : Nat) : String :=
    ", ".intercalate ds ++ (if n > ds.length then s!" and {n - ds.length} more" else "")
  let read := f.listed - f.unread.size
  let first :=
    if f.listed == 0 then s!"Other devices checked {ago} ago: no other backup in iCloud yet."
    else if f.unread.isEmpty then s!"Other devices checked {ago} ago: in step with {backups f.listed}."
    else s!"Other devices checked {ago} ago: {read} of {backups f.listed} read."
  let mut lines := [first]
  if count .keyMissing > 0 then
    lines := lines ++ [s!"Waiting for the key of {backups (count .keyMissing)} (saved {dates (← saved .keyMissing) (count .keyMissing)}): it comes through iCloud Keychain, so check Passwords & Keychain on both devices."]
  if count .notOpened > 0 then
    lines := lines ++ [s!"{backups (count .notOpened)} (saved {dates (← saved .notOpened) (count .notOpened)}) could not be opened and nothing is taken from {if count .notOpened == 1 then "it" else "them"}: made by another version of Winnow, or damaged."]
  if count .notFetched > 0 then
    lines := lines ++ [s!"iCloud did not hand over {backups (count .notFetched)} this time; Winnow will ask again."]
  if f.skipped > 0 then
    lines := lines ++ [s!"{f.skipped} {if f.skipped == 1 then "account or signer" else "accounts or signers"} in those backups {if f.skipped == 1 then "is" else "are"} of a kind this version does not keep."]
  return " ".intercalate lines

/-- The status the screens read, with its dates rendered. -/
def status (a : CloudApp) : IO CloudStatus := do
  let s ← a.controller.get
  let lastSavedText ← match s.lastSaved with
    | some d => some <$> formatReferenceDate d
    | none => pure none
  let now ← unixNowFloat
  -- `lastSaved` counts from 2001 (Foundation's reference date)
  let lastSavedAgo := s.lastSaved.map fun d => relativeAgo (max 0 (now - (d + 978_307_200))).toUInt64.toNat
  -- a backup of a wallet already kept here is not one to restore: it is left out of the list
  let labels ← a.labels.get
  let held := (← a.env.get).held.map (·.id)
  let label (b : CloudBackupSummary) : Option String :=
    (labels.find? fun (id, savedAt, _) => id == b.id && savedAt == b.savedAt).bind (·.2.2)
  let offered := s.available.toList.filter fun b => !((label b).map held.contains).getD false
  let available ← offered.mapM fun b => do
    return ({ id := b.id, savedAtText := ← formatReferenceDate b.savedAt, walletID := label b } : CloudBackupInfo)
  let follow ← a.follow.status.get
  let devicesNote ← if !a.allows || !s.automaticEnabled then pure none else
    match follow.message, follow.checkedAt with
    | some m, _ => pure (some m)
    | none, some t => some <$> devicesText follow (relativeAgo (now.toUInt64.toNat - t))
    | none, none => pure none
  return { automaticEnabled := s.automaticEnabled, enabled := s.enabled, statusTitle := s.statusTitle, lastSavedText, lastSavedAgo,
           issue := s.issue, busy := s.busy, available, restoreNotice := ← a.restoreNotice.get, devicesNote }

/-- The backend's iCloud fields over this app (creation and import prepare the backup inside the
authentication that read the words). -/
def install (a : CloudApp) (base : Backend) : Backend :=
  { base with
    createWallet := fun n dir => do
      let (id, words) ← createWallet a.env n dir
      a.prepare words
      finishOnboarding a.env
      return id
    importBundle := fun n dir json => do
      importBundle a.env n dir json fun bundle _ => do
        if let some words := bundle.mnemonic then a.prepare words
    -- the app's own Remove is what removes an account or a signer on the person's other devices
    removeMultisigAccount := fun id => do
      let had := (← a.multisig.host.read).records.any (·.id == id)
      base.removeMultisigAccount id
      if had then a.follow.noteAccountRemoved id
    removeSigner := fun id => do
      let store ← a.multisig.signers.read
      let key ← match store.records.find? (·.id == id) with
        | some r => signerKey r store.network
        | none => pure none
      base.removeSigner id
      if let some key := key then a.follow.noteSignerRemoved key
    cloudStatus := a.status
    observeCloud := fun k => a.controller.observers.modify (·.push (do k (← a.status)))
    discoverCloudBackups := a.discover
    setAutomaticCloudBackup := a.setAutomatic
    restoreCloudBackup := fun n dir id => do
      match ← (a.restore n dir id).run with
      | .ok r => return .restored r.walletID r.matchesBundle r.context
      | .error .cancelled => return .cancelled
      | .error e => throw (IO.userError e.description)
    cloudTick := a.tick
    cloudScene := a.sceneChanged
    suspendCloud := a.controller.suspend }

end CloudApp
end Real

/-- The real backend with automatic iCloud backup over `store` and `keys` (the shell's CloudKit and iCloud
Keychain on the phone; memory versions in tests). `allows` is false in test mode. -/
def Backend.realWithCloud (deps : Real.Deps) (ledger : IO Real.LedgerSession := Real.noLedger)
    (store : Real.CloudBackupStore) (keys : Real.CloudBackupKeys) (allows : Bool := true)
    (authenticate : String → IO Unit := fun _ => pure ()) (scheduleDelayMs : Nat := 5_000)
    (devicesIntervalMs : Nat := 60_000) : IO (Backend × Real.Env × Real.CloudApp) := do
  let controller ← Real.CloudBackupController.new store keys scheduleDelayMs
  let appRef ← IO.mkRef (none : Option Real.CloudApp)
  let deps := { deps with hooks := { deps.hooks with walletChanged := do
    if let some a ← appRef.get then a.walletChanged } }
  let host ← Real.RecordsHost.new deps.keyStore deps.journal
  let multisig ← Real.MultisigApp.new (RecordsReal.StoreKeyVault.ofKeyStore deps.keyStore) ledger
  let env ← Real.Env.new { deps with hooks := multisig.allHooks host.hooks |> fun h =>
    { h with walletChanged := deps.hooks.walletChanged
             headStart := do if let some a ← appRef.get then a.follow.headStart } }
  multisig.env.set (some env)
  let ctx := host.ctx env
  let base := multisig.install env (ctx.install env.backend)
  let base := { base with records := host.withStore {} fun _ => ctx.records }
  let follow ← Real.SyncApp.new controller env multisig allows devicesIntervalMs
  let app ← Real.CloudApp.new controller env host multisig follow allows authenticate
  follow.changed.set app.scheduleBackup
  appRef.set (some app)
  return (app.install base, env, app)

end WinnowApp
