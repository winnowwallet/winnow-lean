import LeanNative.Native
import WinnowApp.View
import WinnowApp.Update
import WinnowApp.Backend
import WinnowApp.Sample
import WinnowApp.Real
import WinnowApp.E2E

/-! The Winnow app in LeanNative native mode: the model and screens (Update, View and the area modules),
the commands run by `perform` against the `Backend` (the Lean wallet and network) and the shell's
capabilities (auth, clipboard, open). -/

namespace WinnowApp
open LeanNative LeanNative.Native Lean

/-- Where the app keeps its files: `<Application Support>/BTCSwift`, as the Swift app did. -/
initialize rootDir : IO.Ref String ← IO.mkRef ""
/-- The temporary directory (`paths.tmp`): backup files are staged there for the share sheet. -/
initialize tmpDir : IO.Ref String ← IO.mkRef ""
initialize backendRef : IO.Ref Backend ← IO.mkRef Backend.pending
/-- The running status watcher's token: starting or stopping networking bumps it, ending the old one. -/
initialize watcherToken : IO.Ref Nat ← IO.mkRef 0
/-- The background checks running, by task identifier (`BackgroundSyncRun`). -/
initialize backgroundRuns : IO.Ref (List (String × Real.BackgroundSyncRun)) ← IO.mkRef []
/-- Test mode (`E2E.lean`), resolved at boot in a Debug build only. -/
initialize e2eRef : IO.Ref (Option E2E.Mode) ← IO.mkRef none
/-- `<Application Support>` itself: test mode's journal lives in its run directory there. -/
initialize supportDir : IO.Ref String ← IO.mkRef ""
/-- A Debug build, as the shell's `build` capability answers at boot. Test mode, sample data and tracing
are Debug-only: a Release build ignores their environment variables. -/
initialize debugBuild : IO.Ref Bool ← IO.mkRef false

/-- `e2e?.journal(_:fields:)`: nothing outside test mode. -/
def journal (name : String) (fields : List (String × String) := []) : IO Unit := do
  if let some m ← e2eRef.get then m.journal (← supportDir.get) name fields

/-- The launch-environment names test mode reads. -/
def e2eVariables : List String :=
  ["WINNOW_E2E", "WINNOW_E2E_ENTROPY", "WINNOW_E2E_MNEMONIC", "WINNOW_E2E_RUN", "WINNOW_E2E_PEER",
   "WINNOW_E2E_CHALLENGE", "WINNOW_E2E_RESET", "WINNOW_E2E_CLIPBOARD", "WINNOW_E2E_NETWORK", "WINNOW_E2E_TAB",
   "WINNOW_E2E_DEVICE_AUTH", "WINNOW_E2E_ADVANCED", "WINNOW_E2E_CONTROL_FILE", "WINNOW_E2E_PEER_COUNT",
   "WINNOW_E2E_SYNC_INTERVAL", "WINNOW_E2E_LEDGER", "WINNOW_E2E_LIVE_GATEWAYS"]

/-- `E2EMode.current` in a Debug build: inactive, active, or — without pinned entropy — a stop, because a
capture run that generated a real seed would publish it. -/
def resolveE2E : IO (Option E2E.Mode) := do
  let mut env : List (String × String) := []
  for k in e2eVariables do
    if let some v ← IO.getEnv k then env := (k, v) :: env
  match E2E.resolve (fun k => env.lookup k) with
  | .inactive => return none
  | .active m =>
    if m.ledgerEntropy == some none then
      IO.eprintln "WINNOW_E2E_LEDGER is not 16 to 32 bytes of hex entropy. A run asked for the simulated Ledger must not reach for a real one."
      IO.Process.exit 1
    return some m
  | .missingPinnedEntropy =>
    IO.eprintln "WINNOW_E2E=1 without a readable WINNOW_E2E_ENTROPY or WINNOW_E2E_MNEMONIC. A capture run must never generate a real seed: its screenshots are published."
    IO.Process.exit 1

def settingsPath : IO System.FilePath := return System.FilePath.mk (← rootDir.get) / "settings.json"
def walletDir (n : Network) : IO String := return ((System.FilePath.mk (← rootDir.get)) / n.name).toString

def loadSettings : IO Settings := do
  let p ← settingsPath
  if !(← p.pathExists) then return {}
  match Json.parse (← IO.FS.readFile p) >>= fromJson? with
  | .ok s => pure s
  | .error _ => pure {}

/-- The settings and whether they name a network (test mode starts on signet when they do not). -/
def loadSettingsNoting : IO (Settings × Bool) := do
  let p ← settingsPath
  if !(← p.pathExists) then return ({}, false)
  match Json.parse (← IO.FS.readFile p) with
  | .ok j => return ((fromJson? j).toOption.getD {}, (j.getObjVal? "network").isOk)
  | .error _ => return ({}, false)

def trace (msg : String) : IO Unit := do
  if (← debugBuild.get) && (← IO.getEnv "WINNOW_LEAN_TRACE") == some "1" then IO.eprintln s!"[trace] {msg}"

/-- Run `act` in a task and post its answer, or `failed gen ctx message`. -/
def background (fx : Effects Host) (gen : Nat) (ctx : String) (act : IO Host) : IO Unit :=
  discard <| IO.asTask do
    try fx.post (← act) catch e => do trace s!"failed {gen} {ctx}: {e}"; fx.post (.failed gen ctx (toString e))

/-- `authenticateSensitiveAction`: device-owner authentication before `act` (inside a task). A
cancelled prompt is a decision, not a failure: `ctx ++ ".cancelled"` clears the busy state quietly. -/
def authenticated (fx : Effects Host) (gen : Nat) (ctx reason : String) (act : IO Host) : IO Unit :=
  discard <| IO.asTask do
    -- automated Debug runs skip it unless they ask for it (`WINNOW_E2E_DEVICE_AUTH=1`)
    if let some m ← e2eRef.get then
      if !m.requireDeviceAuthentication then
        try fx.post (← act) catch e => fx.post (.failed gen ctx (toString e))
        return
    let auth ← IO.wait (← fx.ask "auth" (Json.mkObj [("reason", Json.str reason)]))
    if (auth.getObjValAs? Bool "ok").toOption.getD false then
      try fx.post (← act) catch e => fx.post (.failed gen ctx (toString e))
    else
      let err := (auth.getObjValAs? String "error").toOption.getD "Device authentication failed."
      let cancelled := (err.toLower.splitOn "cancel").length > 1
      fx.post (.failed gen (if cancelled then ctx ++ ".cancelled" else ctx) err)

/-- `authenticateSensitiveAction(reason:)` for the backend's own flows (the iCloud backup's preparation
and restore): throws when the owner declines or cancels. Skipped in automated Debug runs, as `authenticated`. -/
def authenticateNow (fx : Effects Host) (reason : String) : IO Unit := do
  if let some m ← e2eRef.get then
    if !m.requireDeviceAuthentication then return
  let auth ← IO.wait (← fx.ask "auth" (Json.mkObj [("reason", Json.str reason)]))
  unless (auth.getObjValAs? Bool "ok").toOption.getD false do
    throw (IO.userError ((auth.getObjValAs? String "error").toOption.getD "Device authentication failed."))

def clipPolicyArgs (text : String) : ClipPolicy → Json
  -- the shell's `clipboard.set` takes `text`; the policy rides along for a shell that honours it
  | .recoveryPhrase => Json.mkObj [("text", Json.str text), ("localOnly", Json.bool true), ("expiresIn", toJson (120 : Nat))]
  | .interchange => Json.mkObj [("text", Json.str text), ("localOnly", Json.bool false), ("expiresIn", toJson (300 : Nat))]

/-- The backend, chosen once at boot: `Backend.real` over the shell's Keychain and `http.get`
capabilities. `WINNOW_LEAN_SAMPLE=1` (passed with `SIMCTL_CHILD_` by `simctl launch`) runs the screens
on sample data instead — a UI harness like Winnow's E2EMode (Debug builds only). -/
def chooseBackend (fx : Effects Host) (mode : Option E2E.Mode := none) : IO Unit := do
  if (← debugBuild.get) && (← IO.getEnv "WINNOW_LEAN_SAMPLE") == some "1" then backendRef.set Backend.sample
  else
    let service := (mode.map (·.keychainService)).getD Real.walletService
    let deps : Real.Deps := { keyStore := Real.shellKeyStore fx.ask service, fetch := Real.shellFetch fx.ask,
                              discoverGateways := some (Winnow.IO.discoverGateways) }
    let deps := match mode with
      | none => deps
      | some m =>
        { deps with
          peerCount := m.peerCount.getD deps.peerCount
          syncIntervalMs := (m.syncIntervalSeconds.map fun s => (s * 1000).toUInt64.toNat).getD deps.syncIntervalMs
          networkParams := m.networkParams
          entropy := m.entropy
          journal := fun n f => journal n f
          -- UI journeys never probe the developer's real tailnet, except the live gateway journey
          discoverGateways := if m.liveGateways then deps.discoverGateways else none }
    -- the Ledger: Bluetooth through the shell, or test mode's simulated device with its pinned seed
    let ledger ← match mode.bind (·.ledgerEntropy) |>.join with
      | some entropy =>
        match Winnow.Keys.BIP39.mnemonic entropy with
        | .ok words =>
          match Winnow.Keys.HDKey.ofSeed (Winnow.Keys.BIP39.seed words) with
          | .ok master =>
            -- a test locked to regtest gets a device that shows regtest addresses
            let network := (mode.bind (·.forcedNetwork)).map Real.Network.tx |>.getD .signet
            let device ← IO.mkRef (Winnow.Ledger.Simulator.new master network)
            pure (Real.simulatedLedger device)
          | .error _ => pure Real.noLedger
        | .error _ => pure Real.noLedger
      | none => pure (Real.openLedger fx.ask)
    -- automatic iCloud backup through the shell's CloudKit and iCloud Keychain; never in test mode
    let (b, _, _) ← Backend.realWithCloud deps ledger (Real.shellCloudStore fx.ask) (Real.shellCloudKeys fx.ask)
      (allows := mode.isNone) (authenticate := authenticateNow fx)
    b.observeCloud fun st => fx.post (.cloud st)
    backendRef.set b

/-- `perform`'s trace line for the commands worth following (`WINNOW_LEAN_TRACE=1`, Debug only). -/
def traceCmd : Cmd → IO Unit
  | .refresh g => trace s!"refresh {g}"
  | .syncNow g => trace s!"syncNow {g}"
  | .exportBundle g _ _ name => trace s!"exportBundle {g} {name}"
  | .removeExport file => trace s!"removeExport {file}"
  | .startNetworking g _ => trace s!"startNetworking {g}"
  | .stopNetworking => trace "stopNetworking"
  | .openWallet g _ _ => trace s!"openWallet {g}"
  | _ => pure ()

/-- People and labels changed: the records after `r`, with what the screen does next. -/
def recordsAfter (g : Nat) (d : Done) (r : IO Records) : IO Host := do return .updated g d (← r)

/-- `boot()`: the build and paths, test mode, the backend, the storage directory and the settings. -/
def bootApp (fx : Effects Host) : IO Unit := discard <| IO.asTask do
  let build := (← IO.wait (← fx.ask "build" Json.null))
  let debug := (build.getObjValAs? Bool "debug").toOption.getD false
  debugBuild.set debug
  let mode ← if debug then resolveE2E else pure none
  let paths := (← IO.wait (← fx.ask "paths" Json.null))
  let support := (paths.getObjValAs? String "support").toOption.getD "."
  supportDir.set support
  let root := System.FilePath.mk support / ((mode.map (·.storageDirectoryName)).getD "BTCSwift")
  if let some m := mode then
    -- `wipeIfRequested()`: this run's storage and its Keychain namespace
    if m.reset then
      try IO.FS.removeDirAll root catch _ => pure ()
      discard <| IO.wait (← fx.ask "keychain.clear" (Json.mkObj [("service", Json.str m.keychainService)]))
  e2eRef.set mode
  chooseBackend fx mode
  IO.FS.createDirAll root
  let _ ← fx.ask "exclude-from-backup" (Json.mkObj [("path", Json.str root.toString)])
  rootDir.set root.toString
  -- `ExportStagingFile.sweep()`: a crash with the export sheet open leaves a file that may hold the phrase
  let tmp := (paths.getObjValAs? String "tmp").toOption.getD ""
  tmpDir.set tmp
  unless tmp.isEmpty do Winnow.ExportStagingFile.sweep tmp
  let settings ← match mode with
    | none => loadSettings
    | some m => do
      let (s, hadNetwork) ← loadSettingsNoting
      -- the fixture is a signet (or a forced network); advanced mode and the local node as the only peer
      let network := m.forcedNetwork.getD (if hadNetwork then s.network else .signet)
      let s := { s with network, advancedMode := s.advancedMode || m.advancedMode }
      let s := match m.peer with
        | some p => if s.scoped.manualPeers.contains p then s else s.withScoped fun n => { n with manualPeers := [p] }
        | none => s
      IO.FS.writeFile (← settingsPath) (toJson s).pretty
      if let some text := m.clipboard then
        discard <| IO.wait (← fx.ask "clipboard.set" (Json.mkObj [("text", Json.str text)]))
      let tab := match m.initialTab with | some "send" => 1 | some "settings" => 2 | _ => 0
      fx.post (.launched m.forcedNetwork tab)
      journal "app.initialized" [("network", s.network.name)]
      pure s
  fx.post (.settingsLoaded settings)

/-- The wallet itself: settings, opening, creating, importing and deleting it. -/
def performWallet (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .saveSettings s => discard <| IO.asTask do
      IO.FS.writeFile (← settingsPath) (toJson s).pretty
      b.updateSettings s
  | .openWallet g n isBoot => background fx g "open" do
      let dir ← walletDir n
      IO.FS.createDirAll dir
      let r ← b.openWallet n dir
      if isBoot then
        -- `boot()`: a resumed backup, then the stage it lands on (a damaged store journals nothing)
        match r with
        | .opened id => journal "app.booted" [("stage", "ready"), ("walletID", id)]
        | .missing => journal "app.booted" [("stage", "onboarding"), ("walletID", "")]
        | .damaged _ => pure ()
      return .booted g r
  | .createWallet g n => authenticated fx g "create" "Create and protect your wallet" do
      return .created g (← b.createWallet n (← walletDir n))
  | .importWallet g n json =>
    let act : IO Host := do
      let (id, report) ← b.importBundle n (← walletDir n) json
      return .imported g id report
    -- a bundle carrying recovery words is imported only after device authentication, as AppModel
    let seeded := match Json.parse json with
      | .ok j => match j.getObjVal? "mnemonic" with | .ok .null | .error _ => false | .ok _ => true
      | .error _ => false
    if seeded then authenticated fx g "import" "Import this wallet's recovery phrase" act
    else background fx g "import" act
  | .finishOnboarding _ => discard <| IO.asTask b.finishOnboarding
  | .deleteWallet g => background fx g "delete" do
      b.deleteWallet
      return .deleted g
  | _ => pure ()

/-- Syncing: refreshes, the peers and the networking with its status watcher. -/
def performSync (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .refresh g => do
      background fx g "refresh" do
        let (s, p) ← b.snapshot
        return .snapshot g s p
      background fx g "refresh" do return .records g (← b.records)
      background fx g "multisigOverview" do return .multisig g (← b.multisigOverview)
      -- `refresh()` ends by scheduling the iCloud backup's update (and a preparation when due)
      discard <| IO.asTask (try b.cloudTick catch _ => pure ())
  | .syncNow g => background fx g "sync" do
      b.syncNow
      let (s, p) ← b.snapshot
      return .snapshot g s p
  | .retryPeers g => background fx g "sync" do
      b.retryPeers
      let (s, p) ← b.snapshot
      return .snapshot g s p
  | .reconnect g s => background fx g "sync" do
      b.reconnect s
      let (st, p) ← b.snapshot
      return .snapshot g st p
  | .startNetworking g s => do
      discard <| IO.asTask (b.startNetworking s)
      -- AppModel's 1 s `phaseTask`: what the sync loop changed reaches the model as a snapshot
      let token ← watcherToken.modifyGet fun t => (t + 1, t + 1)
      discard <| IO.asTask do
        let mut last := ""
        let mut lastMultisig : Option MultisigOverview := none
        while (← watcherToken.get) == token do
          try
            let (st, p) ← b.snapshot
            let key := reprStr (st, p)
            if key != last then
              last := key
              try b.cloudTick catch _ => pure ()
              trace s!"watcher {g} posts balance {st.balance} peers {st.peerCount} tip {st.tipHeight} scan {st.nextScanHeight} error {st.lastSyncError}"
              fx.post (.snapshot g st p)
            -- `refresh()` also mirrors `multisigAccounts`: what the sync credited reaches the screens
            let o ← b.multisigOverview
            if lastMultisig != some o then
              lastMultisig := some o
              fx.post (.multisig g o)
          catch e => trace s!"watcher {g}: {e}"
          IO.sleep 1000
  | .stopNetworking => do
      watcherToken.modify (· + 1)
      discard <| IO.asTask b.stopNetworking
  | _ => pure ()

/-- Receiving, sending, a payment's details and a fee bump. -/
def performPayments (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .receiveAddress g fresh => background fx g "receive" do return .receiveAddress g (← b.receiveAddress fresh)
  | .watchAddress g address => discard <| IO.asTask do
      try b.watchAddress address (fun txid amount => fx.post (.unconfirmed g address txid amount)) catch _ => pure ()
  | .stopWatchingAddress => discard <| IO.asTask b.stopWatchingAddress
  | .setReceiveLabel g address label => background fx g "label" (recordsAfter g .labelSaved (b.setReceiveLabel address label))
  | .resolveRate g inputs _ => background fx g "rate" do
      return .resolvedRate g inputs (← b.resolveFeeRate inputs.priority (parseRateMilli inputs.override))
  | .previewSend g inputs => background fx g "send" do return .previewed g inputs (← b.previewSend inputs)
  | .sendPayment g inputs p =>
      authenticated fx g "send" s!"Send {satsText p.amount} to {p.destination}" do
        let r ← b.sendPayment inputs p
        return .sent g r.txid r.derivedAddresses
  | .rawTransaction g txid => background fx g "refresh" do return .rawTransaction g txid (← b.rawTransactionHex txid)
  | .watchRelay g txid => discard <| IO.asTask do
      try b.watchRelay txid (fun e => fx.post (.relay g txid e)) catch _ => pure ()
  | .loadPaymentDetails g txid => background fx g "payment" do
      b.loadPaymentDetails txid
      return .paymentLoaded g txid
  | .pendingFeeRate g txid => background fx g "feeBump" do
      let (milli, suggested) ← b.pendingFeeRate txid
      return .pendingRate g txid milli suggested
  | .previewFeeBump g txid text milli => background fx g "feeBump" do
      return .bumpPreviewed g txid text (← b.previewFeeBump txid milli)
  | .bumpFee g txid p =>
      authenticated fx g "feeBump" "Replace this transaction with a higher fee" do
        return .bumped g txid (← b.bumpFee txid p)
  | _ => pure ()

/-- Settings: the peer catalog and peers, the backup file, the recovery phrase and the person card. -/
def performSettings (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .catalogStatus g => background fx g "catalog" do return .catalogStored g (← b.catalogStatus)
  | .connectedPeers g => background fx g "peers" do return .peers g (← b.connectedPeers)
  | .resetPeers g => background fx g "peers" do
      b.resetPeers
      return .peersReset g
  | .exportBundle g e withPhrase name => background fx g "export" do
      let text ← b.exportBundle withPhrase
      let staging ← Winnow.ExportStagingFile.new (← tmpDir.get)
      let file ← staging.write text name
      -- `protect`: the file and its directory are excluded from backup and readable only while unlocked
      for p in [file, file.parent.getD file] do
        let r ← IO.wait (← fx.ask "exclude-from-backup" (Json.mkObj [("path", Json.str p.toString), ("complete", Json.bool true)]))
        unless (r.getObjValAs? Bool "ok").toOption.getD false do
          staging.remove
          throw (IO.userError "The backup file could not be protected on this device.")
      return .exported g e file.toString
  | .removeExport file => discard <| IO.asTask do
      -- only a staging directory, never anything else a stale path could name
      let some dir := (System.FilePath.mk file).parent | return
      if (dir.fileName.getD "").startsWith Winnow.ExportStagingFile.prefix_ then
        try IO.FS.removeDirAll dir catch _ => pure ()
  | .revealPhrase g e =>
      authenticated fx g "reveal" "Show your recovery phrase" do
        let words ← b.revealMnemonic
        let required := (← e2eRef.get).any (·.requireDeviceAuthentication)
        journal "backup.phraseRevealReady" [("deviceAuthenticationRequired", toString required)]
        return .revealed g e words
  | .ownCard g name => background fx g "card" do return .card g name (← b.ownCard name)
  | _ => pure ()

/-- People and sender labels. -/
def performPeople (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .parsePaste g text => discard <| IO.asTask do
      try fx.post (.pasteParsed g text (.ok (← b.parsePaste text)))
      catch e => fx.post (.pasteParsed g text (.error (toString e)))
  | .addPerson g name paste prov source labelTxid => background fx g "person" do
      return .updated g (if labelTxid.isSome then .senderLabeled else .personSaved)
        (← b.addPerson name paste prov source labelTxid)
  | .editPerson g pid name attach => background fx g "person" do
      if let some (paste, prov, source) := attach then discard <| b.attachDestination pid paste prov source
      return .updated g .personSaved (← b.updateRecipient pid (some name) true)
  | .updateRecipient g pid name saved ctx => background fx g ctx (recordsAfter g .none (b.updateRecipient pid name saved))
  | .labelSender g txid pid => background fx g "person" (recordsAfter g .senderLabeled (b.labelSender txid pid))
  | .removeSenderLabel g txid => background fx g "payment" (recordsAfter g .none (b.removeSenderLabel txid))
  | .lookupSender g txid base => background fx g "person" do return .senderLookup g txid base (← b.lookupSender txid base)
  | _ => pure ()

/-- Multisig accounts, their drafts, the Ledger and saved signers. -/
def performMultisig (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .multisigOverview g => background fx g "multisigOverview" do return .multisig g (← b.multisigOverview)
  | .checkMultisigDescriptor g text => discard <| IO.asTask do
      try fx.post (.multisigChecked g text (.ok (← b.checkMultisigDescriptor text)))
      catch e => fx.post (.multisigChecked g text (.error (toString e)))
  | .addMultisigAccount g adv name d => background fx g "multisigAdd" do
      let (id, registration) ← b.addMultisigAccount adv name d
      return .multisigAdded g id registration
  | .removeMultisigAccount g id => background fx g "multisigAccount" do
      b.removeMultisigAccount id
      return .multisigRemoved g id
  | .newMultisigAddress g id => background fx g "multisigAccount" do
      b.newMultisigReceiveAddress id
      return .multisig g (← b.multisigOverview)
  | .createMultisigAccount g adv name k members rec => background fx g "multisigBuild" do
      let (id, d, registration) ← b.createMultisigAccount adv name k members rec
      return .multisigCreated g id d registration
  | .registerLedger g adv id => discard <| IO.asTask do
      try
        b.registerLedger adv id
        fx.post (.ledgerRegistered g id (.ok ()))
      catch e => fx.post (.ledgerRegistered g id (.error (toString e)))
  | .pairLedger g adv name => background fx g "ledgerPair" do return .ledgerPaired g (← b.pairLedger adv name)
  | .addSignerKeys g adv name text => background fx g "signerKeys" do
      return .signerSaved g (← b.addSignerKeys adv name text)
  | .renameSigner g id name => background fx g "signer" do
      b.renameSigner id name
      return .signerRenamed g id
  | .removeSigner g id => background fx g "signer" do
      b.removeSigner id
      return .signerRemoved g id
  | .verifyLedgerAddress g adv id index => discard <| IO.asTask do
      try fx.post (.ledgerAddressShown g id index (.ok (← b.verifyLedgerAddress adv id index)))
      catch e => fx.post (.ledgerAddressShown g id index (.error (toString e)))
  | .signAndDraft g adv inputs p =>
      -- "Sign and continue": one device authentication, this phone's signature, the draft filed
      authenticated fx g "send" "Sign this multisig payment" do
        return .drafted g (← b.signAndDraft adv inputs p)
  | .signDraft g e id =>
      authenticated fx g s!"collect.{e}" "Sign this multisig payment" do
        b.signDraft id
        return .collected g e id
  | .signDraftWithLedger g e adv id => background fx g s!"collect.{e}" do
      b.signDraftWithLedger adv id
      return .collected g e id
  | .adoptDraft g e id psbt => background fx g s!"collect.{e}" do
      b.adoptDraft id psbt
      return .collected g e id true
  | .broadcastDraft g e id => background fx g s!"collect.{e}" do
      return .draftBroadcast g e id (← b.broadcastDraft id)
  | .discardDraft g e id => background fx g s!"collect.{e}" do
      b.discardDraft id
      return .collected g e id
  | .rebroadcastSpend g id txid => background fx g "accountSpend" do
      b.rebroadcastSpend id txid
      return .spendHandled g id txid
  | .abandonSpend g id txid => background fx g "accountSpend" do
      b.abandonSpend id txid
      return .spendHandled g id txid
  | _ => pure ()

/-- The shell's capabilities: the clipboard, timers, links, the journal, iCloud and background tasks. -/
def performShell (b : Backend) (fx : Effects Host) (c : Cmd) : IO Unit := do
  match c with
  | .copy text policy => fx.cap "clipboard.set" (clipPolicyArgs text policy) fun _ => .copiedExpired ""
  | .timer ms h => discard <| IO.asTask do
      IO.sleep ms.toUInt32
      fx.post h
  | .openURL url => fx.cap "open" (Json.mkObj [("url", Json.str url)]) fun _ => .copiedExpired ""
  | .journal name fields => journal name fields
  | .discoverCloud => discard <| IO.asTask (try b.discoverCloudBackups catch _ => pure ())
  | .setAutomaticCloud enabled => discard <| IO.asTask (try b.setAutomaticCloudBackup enabled catch _ => pure ())
  | .restoreCloud g n id => background fx g "cloudRestore" do
      let (walletID, verified, context) ← b.restoreCloudBackup n (← walletDir n) id
      return .cloudRestored g walletID verified context
  | .suspendCloud => discard <| IO.asTask b.suspendCloud
  | .cloudScene active => discard <| IO.asTask (try b.cloudScene active catch _ => pure ())
  | .scheduleBackgroundTasks => discard <| IO.asTask do
      -- replacing our own requests keeps one of each pending; a refused request (Background App Refresh
      -- off, or the simulator) changes nothing: Settings shows when the chain was last checked
      discard <| fx.ask "bgtask.schedule" (Json.mkObj [("id", Json.str Real.backgroundRefreshID), ("kind", Json.str "refresh"),
        ("after", toJson (900 : Nat))])
      discard <| fx.ask "bgtask.schedule" (Json.mkObj [("id", Json.str Real.backgroundProcessingID), ("kind", Json.str "processing"),
        ("after", toJson (900 : Nat)), ("requiresNetwork", Json.bool true), ("requiresPower", Json.bool false)])
  | .runBackgroundTask id kind s => do
      let complete (success : Bool) : IO Unit := do
        backgroundRuns.modify (·.filter (·.1 != id))
        discard <| fx.ask "bgtask.complete" (Json.mkObj [("id", Json.str id), ("success", Json.bool success)])
      let run ← Real.BackgroundSyncRun.new (Real.backgroundBudgetMs kind) (b.runBackgroundSync s) b.cancelBackgroundSync complete
      backgroundRuns.modify ((id, run) :: ·)
      run.start
  | .expireBackgroundTask id => do
      match (← backgroundRuns.get).lookup id with
      | some run => run.expire
      -- expired before it started: it completes unsuccessfully
      | none => discard <| fx.ask "bgtask.complete" (Json.mkObj [("id", Json.str id), ("success", Json.bool false)])
  | .backgroundRefreshStatus =>
    fx.cap "bgtask.refreshStatus" Json.null fun r =>
      .backgroundRefresh ((r.getObjValAs? String "status").toOption.getD "available" == "available")
  | .paste target => discard <| IO.asTask do
      -- `pasteboardText()`: the runner's control file under test mode, the pasteboard otherwise
      let fromControl ← match ← e2eRef.get with
        | some m => pure ((← m.control).bind (·.clipboard))
        | none => pure none
      match fromControl with
      | some text => fx.post (.pasted target text)
      | none =>
        let j ← IO.wait (← fx.ask "clipboard.get" Json.null)
        fx.post (.pasted target ((j.getObjValAs? String "text").toOption.getD ""))
  | _ => pure ()

def perform (c : Cmd) (fx : Effects Host) : IO Unit := do
  traceCmd c
  let b ← backendRef.get
  match c with
  | .boot => bootApp fx
  | .saveSettings .. | .openWallet .. | .createWallet .. | .importWallet .. | .finishOnboarding ..
  | .deleteWallet .. =>
    performWallet b fx c
  | .refresh .. | .syncNow .. | .retryPeers .. | .reconnect .. | .startNetworking .. | .stopNetworking =>
    performSync b fx c
  | .receiveAddress .. | .watchAddress .. | .stopWatchingAddress | .setReceiveLabel .. | .resolveRate ..
  | .previewSend .. | .sendPayment .. | .rawTransaction .. | .watchRelay .. | .loadPaymentDetails ..
  | .pendingFeeRate .. | .previewFeeBump .. | .bumpFee .. =>
    performPayments b fx c
  | .catalogStatus .. | .connectedPeers .. | .resetPeers .. | .exportBundle .. | .removeExport ..
  | .revealPhrase .. | .ownCard .. =>
    performSettings b fx c
  | .parsePaste .. | .addPerson .. | .editPerson .. | .updateRecipient .. | .labelSender ..
  | .removeSenderLabel .. | .lookupSender .. =>
    performPeople b fx c
  | .multisigOverview .. | .checkMultisigDescriptor .. | .addMultisigAccount .. | .removeMultisigAccount ..
  | .newMultisigAddress .. | .createMultisigAccount .. | .registerLedger .. | .pairLedger .. | .addSignerKeys ..
  | .renameSigner .. | .removeSigner .. | .verifyLedgerAddress .. | .signAndDraft .. | .signDraft ..
  | .signDraftWithLedger .. | .adoptDraft .. | .broadcastDraft .. | .discardDraft .. | .rebroadcastSpend ..
  | .abandonSpend .. =>
    performMultisig b fx c
  | .copy .. | .timer .. | .openURL .. | .journal .. | .discoverCloud | .setAutomaticCloud .. | .restoreCloud ..
  | .suspendCloud | .cloudScene .. | .scheduleBackgroundTasks | .runBackgroundTask .. | .expireBackgroundTask ..
  | .backgroundRefreshStatus | .paste .. =>
    performShell b fx c

def app : Native.App Model Msg Cmd Host :=
  { init := {}, update, view, cmds, host := Msg.host, perform := fun c fx => do
      perform c fx
    boot := [.boot], system }

initialize Native.register app

end WinnowApp
