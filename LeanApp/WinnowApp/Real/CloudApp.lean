import WinnowApp.Real.Full
import WinnowApp.Real.CloudBackup
import LeanNative.Native.EffectScope

/-! # AppModel's iCloud backup (the `AppModel` extension in AppModel.swift, upstream d2ca878 :3485–3651)

Automatic backup runs unless turned off, in Simple and Advanced mode, and never decides whether the
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

Test mode never uses iCloud (`allowsCloudBackup`). The context's display name and Advanced switch are the
Model's settings here: a restore hands them back (`CloudRestored.context`) for the Model to save. -/

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

namespace CloudApp

def new (controller : CloudBackupController) (env : Env) (host : RecordsHost) (multisig : MultisigApp) (allows : Bool)
    (authenticate : String → IO Unit) : IO CloudApp := do
  return { controller, env, host, multisig, allows, authenticate, attempted := ← IO.mkRef [], preparing := ← IO.mkRef none,
           preparation := ← LeanNative.Native.EffectScope.new, preparationTask := ← IO.mkRef none, restoreNotice := ← IO.mkRef none, wasActive := ← IO.mkRef false }

def directory (a : CloudApp) : IO (Option System.FilePath) := do return (← a.env.get).dir.map System.FilePath.mk
def walletID (a : CloudApp) : IO (Option String) := do return (← a.env.get).wallet.map (·.id)
def network (a : CloudApp) : IO (Option WinnowApp.Network) := do return (← a.env.get).network

/-- `cloudBackups.configure(directory: storageDirectory(), walletID: walletID)`. -/
def configureCurrent (a : CloudApp) : IO Unit := do
  a.controller.configure (← a.directory) (← a.walletID)

/-- `discoverCloudBackups()`: onboarding's search for this network's saved backups. -/
def discover (a : CloudApp) : IO Unit := do
  if !a.allows || (← a.walletID).isSome then return
  let some n ← a.network | return
  a.controller.discover n.name

/-- `cloudAppState(for:)`: people, receive-address labels, the display name and the Advanced switch,
validated against the bundle. -/
def cloudAppState (a : CloudApp) (bundle : ImportBundle) : IO CloudAppState := do
  let some walletID ← a.walletID | failWith .noWallet
  let store ← a.host.store
  let st ← store.read
  let labels ← store.labelStore st walletID
  let settings := ((← a.env.get).settings).getD {}
  let state : CloudAppState := {
    network := bundle.network, descriptor := bundle.descriptor, people := ← RM.toIO st.people.backup,
    receiveLabels := ← RM.toIO labels.backup, ownDisplayName := settings.ownDisplayName, advancedMode := settings.advancedMode }
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
def cloudContents (a : CloudApp) (words walletID : String) : IO CloudBackupContents := do
  let network ← a.network
  let bundle := { (← a.exportedBundle) with mnemonic := some words }
  let state ← a.cloudAppState bundle
  unless (← a.walletID) == some walletID && (← a.network) == network do throwCancelled
  return { bundle, appState := some state.encoded }

/-- `scheduleCloudBackup()`: after a refresh, while active, for the open wallet. -/
def scheduleBackup (a : CloudApp) : IO Unit := do
  if !a.allows then return
  a.configureCurrent
  let c ← a.env.get
  let (true, some w, network) := (c.active, c.wallet, c.network) | return
  a.controller.schedule do
    unless (← a.walletID) == some w.id && (← a.network) == network do throwCancelled
    let bundle ← a.exportedBundle
    let state ← a.cloudAppState bundle
    unless (← a.walletID) == some w.id && (← a.network) == network do throwCancelled
    return { bundle, appState := some state.encoded }

/-- `prepareCloudBackup(words:account:)`: stage the encrypted copy (only ciphertext) while the
authentication that read the words is valid. Never fails the caller. -/
def prepare (a : CloudApp) (words : String) (account : Option String := none) : IO Unit := do
  if !a.allows then return
  let some walletID ← a.walletID | return
  a.attempted.modify fun l => if l.contains walletID then l else l ++ [walletID]
  a.configureCurrent
  if !(← a.controller.get).needsPreparation then return
  try
    let contents ← a.cloudContents words walletID
    a.controller.prepare contents walletID account
    a.scheduleBackup
  catch e => if !isCancellation e then a.controller.reportPreparationFailure e

/-- `acceptsCloudPreparation(_:network:)`. -/
def accepts (a : CloudApp) (walletID : String) (network : Option WinnowApp.Network) : IO Bool := do
  let c ← a.env.get
  return c.wallet.map (·.id) == some walletID && c.network == network && c.active &&
    (← a.controller.get).needsPreparation

/-- `cloudRecoveryWords(walletID:)`: automatic recovery needs the words; an xprv-only or missing secret is
`unsupportedWallet`. -/
def recoveryWords (a : CloudApp) (walletID : String) : IO String := do
  match ← (a.env.deps.keyStore.load walletID).run with
  | .ok (.mnemonic words) => return words
  | .ok _ | .error (.notFound _) => CloudBackupError.unsupportedWallet.throw
  | .error e => failText (keyStoreErrorText e)

/-- `prepareExistingCloudBackup(walletID:network:)`: the account first (no prompt when iCloud is
unavailable), then authentication, the words, the copy. The preparation's scope is checked before the
prompt, and the words and the copy start only as the scope's task after the answer, so a wallet switch, a
network switch or the background while the person answers ends it before the protected part starts; this
app's own conditions (the same wallet, network, an active scene) are checked with it. -/
def prepareExisting (a : CloudApp) (walletID : String) (network : Option WinnowApp.Network)
    (token : LeanNative.Native.EffectScope.Token) : IO Unit := do
  let live : IO Bool := do return (← a.preparation.isValid token) && (← a.accepts walletID network)
  -- the authentication's own error, as this app reports it
  let declined ← IO.mkRef (none : Option IO.Error)
  let authenticate : IO (LeanNative.Native.Client.Result Unit) := do
    try a.authenticate "Protect your wallet with automatic iCloud backup"; return .ok ()
    catch e =>
      declined.set (some e)
      return .error { kind := .failed, name := "authentication", detail := toString e }
  try
    let account ← a.controller.accountForPreparation
    if !(← live) then return
    let r ← a.preparation.authenticated token authenticate do
      unless ← a.accepts walletID network do return
      let words ← a.recoveryWords walletID
      a.prepare words (some account)
    match r with
    | .done () | .stale _ => pure ()
    | .failed e => throw e
    | .denied _ | .cancelled _ | .error _ =>
      if let some e ← declined.get then throw e
  catch e =>
    if !isCancellation e && (← live) then a.controller.reportPreparationFailure e

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

/-- What `refresh()` asks of the iCloud side: an update of the copy, and a preparation if one is due. -/
def tick (a : CloudApp) : IO Unit := do
  a.scheduleBackup
  a.schedulePreparation

/-- `scenePhaseChanged`: a new foreground session may prepare again; the background cancels preparation
and suspends the controller. -/
def sceneChanged (a : CloudApp) (active : Bool) : IO Unit := do
  let was ← a.wasActive.modifyGet fun w => (w, active)
  if active then
    if !was then a.attempted.set []
  else
    discard <| a.preparation.invalidateWithoutWaiting
    a.preparing.set none
    a.controller.suspend

/-- The wallet changed or went (`adopt`, `destroyWallet`, `switchNetwork`). -/
def walletChanged (a : CloudApp) : IO Unit := do
  -- without waiting: this hook can run inside the preparation's own task (the copy adopts the wallet)
  discard <| a.preparation.invalidateWithoutWaiting
  a.preparing.set none
  a.controller.configure none none

/-- `setAutomaticCloudBackup(_:)` (Advanced's switch). -/
def setAutomatic (a : CloudApp) (enabled : Bool) : IO Unit := do
  let some walletID ← a.walletID | return
  a.configureCurrent
  try
    a.controller.setAutomatic enabled
    if enabled then
      a.attempted.modify (·.erase walletID)
      a.schedulePreparation
      a.scheduleBackup
  catch e => a.controller.reportPreparationFailure e

/-- `applyCloudAppState(_:)`: people, signers and labels restored; the display name and Advanced switch
handed back to the Model. -/
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
replaces a wallet already on this phone. -/
def restore (a : CloudApp) (n : WinnowApp.Network) (dir id : String) : IO CloudRestored := do
  if (← a.walletID).isSome || !a.allows then failWith .noWallet
  a.restoreNotice.set none
  a.authenticate "Restore your wallet and signing key from iCloud"
  let restoration ← a.controller.restoreContents id
  let bundle := restoration.contents.bundle
  let mut appState ← RM.toIO (CloudAppState.decode restoration.contents.appState bundle)
  if let some saved := appState then
    let store ← a.host.store
    let people ← RM.toIO ((← store.read).people.planRestore saved.people)
    let signers ← RM.toIO ((← a.multisig.signers.read).planRestore (saved.signers.getD #[]))
    appState := some { saved with people, signers := some signers }
  unless (← a.walletID).isNone && (← a.network) == some n do throwCancelled
  let validated := appState
  let (walletID, report) ← importDecoded a.env n dir bundle fun restoredID => do
    unless (← a.walletID) == some restoredID && (← a.network) == some n do throwCancelled
    match validated with
    | some state => a.applyAppState state
    | none => a.restoreNotice.set (some "This older backup restores your wallet and key, but does not contain saved people or address labels.")
    a.configureCurrent
    try
      let current ← a.cloudAppState bundle
      a.controller.resume { bundle, appState := some current.encoded } restoredID restoration.account
    catch e => a.controller.reportResumeFailure e
  return { walletID, matchesBundle := report.map (·.matchesBundle),
           context := validated.map fun s => (s.ownDisplayName, s.advancedMode) }

/-- The status the screens read, with its dates rendered. -/
def status (a : CloudApp) : IO CloudStatus := do
  let s ← a.controller.get
  let lastSavedText ← match s.lastSaved with
    | some d => some <$> formatReferenceDate d
    | none => pure none
  let now ← unixNowFloat
  -- `lastSaved` counts from 2001 (Foundation's reference date)
  let lastSavedAgo := s.lastSaved.map fun d => relativeAgo (max 0 (now - (d + 978_307_200))).toUInt64.toNat
  let available ← s.available.toList.mapM fun b => do return ({ id := b.id, savedAtText := ← formatReferenceDate b.savedAt } : CloudBackupInfo)
  return { automaticEnabled := s.automaticEnabled, enabled := s.enabled, statusTitle := s.statusTitle, lastSavedText, lastSavedAgo,
           message := s.message, busy := s.busy, available, restoreNotice := ← a.restoreNotice.get }

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
    cloudStatus := a.status
    observeCloud := fun k => a.controller.observers.modify (·.push (do k (← a.status)))
    discoverCloudBackups := a.discover
    setAutomaticCloudBackup := a.setAutomatic
    restoreCloudBackup := fun n dir id => do
      let r ← a.restore n dir id
      return (r.walletID, r.matchesBundle, r.context)
    cloudTick := a.tick
    cloudScene := a.sceneChanged
    suspendCloud := a.controller.suspend }

end CloudApp
end Real

/-- The real backend with automatic iCloud backup over `store` and `keys` (the shell's CloudKit and iCloud
Keychain on the phone; memory versions in tests). `allows` is false in test mode. -/
def Backend.realWithCloud (deps : Real.Deps) (ledger : IO Real.LedgerSession := Real.noLedger)
    (store : Real.CloudBackupStore) (keys : Real.CloudBackupKeys) (allows : Bool := true)
    (authenticate : String → IO Unit := fun _ => pure ()) (scheduleDelayMs : Nat := 5_000) :
    IO (Backend × Real.Env × Real.CloudApp) := do
  let controller ← Real.CloudBackupController.new store keys scheduleDelayMs
  let appRef ← IO.mkRef (none : Option Real.CloudApp)
  let deps := { deps with hooks := { deps.hooks with walletChanged := do
    if let some a ← appRef.get then a.walletChanged } }
  let host ← Real.RecordsHost.new deps.keyStore deps.journal
  let multisig ← Real.MultisigApp.new (RecordsReal.StoreKeyVault.ofKeyStore deps.keyStore) ledger
  let env ← Real.Env.new { deps with hooks := multisig.allHooks host.hooks |> fun h => { h with walletChanged := deps.hooks.walletChanged } }
  multisig.env.set (some env)
  let ctx := host.ctx env
  let base := multisig.install env (ctx.install env.backend)
  let base := { base with records := host.withStore {} fun _ => ctx.records }
  let app ← Real.CloudApp.new controller env host multisig allows authenticate
  appRef.set (some app)
  return (app.install base, env, app)

end WinnowApp
