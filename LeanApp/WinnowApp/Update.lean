import WinnowApp.Home
import WinnowApp.Send
import WinnowApp.Receive
import WinnowApp.Settings
import WinnowApp.People

/-! `step msg m = (m', cmds)`; `update` and `cmds` of the app are its two halves (same pre-state).
User messages go to their area's `step`; host answers are checked here — a network answer only
for the current generation, a sensitive one only for the current epoch while active. The answer that ends
something the person started (a payment, a fee bump, a saved label or person, the wallet created or
restored) counts for the same wallet (`Model.sameWallet`): the phone may lock before it arrives, and the
payment went out anyway. -/

namespace WinnowApp

/-- Records changed. -/
def Model.onRecords (m : Model) (r : Records) : Model × List Cmd := ({ m with records := r }, [])

/-- Background: networking stops, answers in flight are dropped, sensitive presentations close and
forget (the receive window closes; Receive itself stays). -/
def Model.background (m : Model) : Model × List Cmd :=
  let m0 := m.nextGeneration
  let m1 := { m0 with
    active := false
    onboarding := { m.onboarding with importText := "", busy := false, restoring := false }
    reveal := {}
    exportState := {}
    -- the collection step's answers in flight no longer count
    collect := m.collect.cleared }
  let (m2, cs) := match m1.sheets.findIdx? Sheet.isSensitive with
    | some i => m1.closeFrom i
    | none => (m1, [])
  -- `BackgroundSyncScheduler.shared.schedule()` on every trip to the background
  (m2, [.stopNetworking, .stopWatchingAddress, .scheduleBackgroundTasks, .cloudScene false] ++ m.discardExport ++ cs)

def onHost (h : Host) (m : Model) : Model × List Cmd :=
  let current (g : Nat) := g == m.generation
  let sensitive (g e : Nat) := g == m.generation && e == m.epoch && m.active
  match h with
  | .launched forced tab => ({ m with forcedNetwork := forced, tab := tab }, [])
  | .settingsLoaded s =>
    let m := { m with settings := s }.loadGatewayDraft
    (m, [.openWallet m.generation s.network true])
  | .booted g r =>
    if !current g then (m, []) else
    -- networking runs only while the scene is active (a cold background launch has no scene); a background
    -- task iOS launched during boot runs now
    let start : List Cmd := if m.active then [.startNetworking g m.settings] else []
    let pending : List Cmd := match m.pendingBackgroundTask with
      | some (id, kind) => [.runBackgroundTask id kind m.settings]
      | none => []
    let m := { m with pendingBackgroundTask := none }
    match r with
    | .opened id => ({ m with stage := .ready, walletID := some id }, [.refresh g] ++ start ++ pending)
    -- activation builds the stack whatever the stage, so a new wallet is dated at a synced tip; onboarding
    -- looks for this network's iCloud backups (`.task(id: model.network)`)
    | .missing => ({ m with stage := .onboarding, walletID := none }, start ++ [.discoverCloud] ++ pending)
    | .damaged msg => ({ m with stage := .storageDamaged msg }, pending)
  | .created g id =>
    -- creation finishes onboarding by itself: no phrase checklist, and neither iCloud nor a manual backup
    -- decides whether the wallet can be used
    if !m.sameWallet g then (m, []) else
    let g := m.generation
    ({ m with stage := .ready, walletID := some id, sheets := [], onboarding := ({} : Onboarding) },
     [.refresh g] ++ (if m.active then [.startNetworking g m.settings] else []))
  | .imported g id report =>
    if !m.sameWallet g then (m, []) else
    ({ m with walletID := some id, onboarding := { m.onboarding with busy := false, importReport := some report, error := none } }, [])
  | .cloud st => ({ m with cloud := st }, [])
  | .cloudRestored g id verified context =>
    if !m.sameWallet g then (m, []) else
    let note := match verified with
      | some true => none
      | some false => some "Some payments changed since this backup. Winnow updated the wallet from the network; review the restored balances."
      | none => some "Restored. Network verification will resume when peers are reachable."
    let m := { m with walletID := some id,
                      onboarding := { m.onboarding with restoring := false, restored := true, restoreError := note } }
    match context with
    | some (name, advanced) =>
      -- `setOwnDisplayName`, `setAdvancedMode`: the restored context's two settings
      let s := { m.settings with ownDisplayName := name, advancedMode := advanced }
      ({ m with settings := s }, [.saveSettings s])
    | none => (m, [])
  | .snapshot g s p =>
    if !current g then (m, []) else
    let wasSyncing := m.status.syncing
    let s := { s with history := historyForDisplay s.history }
    let m := { m with status := s, phase := p }
    -- the mempool window owns only the temporary rows: a payment seen in a block drops its row
    let m := { m with receive := { m.receive with unconfirmed := m.receive.unconfirmed.filter fun (t, _) =>
                 !(s.history.any fun e => e.txid == t && e.height > 0) } }
    let m := match m.send.sentTxid with
      | some t => if m.send.confirmedHeight.isNone then
          -- an account's broadcast confirms in the merged list
          match m.historyItem? t with
          | some e => if e.height > 0 then { m with send := { m.send with confirmedHeight := some e.height } } else m
          | none => m
        else m
      | none => m
    if wasSyncing && !s.syncing then m.loadPayment else (m, [])
  | .records g r => if current g then m.onRecords r else (m, [])
  | .updated g d r =>
    if !m.sameWallet g then (m, []) else
    let (m, cs) := m.onRecords r
    let (m, cs2) := match d with
      | .none => (m, [])
      | .personSaved | .senderLabeled => m.closeSheet .addPerson
      | .labelSaved => m.finishLabel
    (m, cs ++ cs2)
  | .receiveAddress g a =>
    if m.sameWallet g && m.hasSheet .receive then m.onReceiveAddress a else (m, [])
  | .unconfirmed g address txid amount =>
    if current g && m.receive.address == address && !(m.receive.unconfirmed.any (·.1 == txid)) then
      ({ m with receive := { m.receive with unconfirmed := m.receive.unconfirmed ++ [(txid, amount)] } }, [])
    else (m, [])
  | .failed g ctx msg => if m.sameWallet g then (m.fail ctx msg, []) else (m, [])
  | .resolvedRate g forInputs milli =>
    let i := m.sendInputs
    if current g && forInputs.priority == i.priority && forInputs.override == i.override then
      ({ m with send := { m.send with resolvedRateMilli := some milli } }, [])
    else (m, [])
  | .previewed g forInputs p =>
    -- a preview counts only for the inputs it was made for (SendReviewInputs)
    if current g && forInputs == m.sendInputs then
      ({ m with send := { m.send with preview := some p, reviewing := false, error := none } }, [])
    else ({ m with send := { m.send with reviewing := false } }, [])
  | .sent g txid derived =>
    if !m.sameWallet g then (m, []) else
    let g := m.generation
    ({ m with send := { m.send with sending := false, sentTxid := some txid, derivedAddresses := derived },
              spendingInFlight := false },
     [.refresh g, .rawTransaction g txid, .watchRelay g txid])
  | .rawTransaction g txid hex =>
    if current g && m.send.sentTxid == some txid then ({ m with send := { m.send with rawTransaction := hex } }, []) else (m, [])
  | .relay g txid e => if current g then (m.onRelay txid e, []) else (m, [])
  | .paymentLoaded g _ =>
    if m.sameWallet g then ({ m with payment := { m.payment with loading := false } }, [.refresh m.generation]) else (m, [])
  | .pendingRate g txid milli text =>
    if !current g || m.feeBump.txid != txid then (m, []) else
    ({ m with feeBump := { m.feeBump with currentRateMilli := some milli, targetText := text } },
     match parseRateMilli text (trimNewlines := true) with | some r => [.previewFeeBump g txid text r] | none => [])
  | .bumpPreviewed g txid text p =>
    if current g && m.feeBump.txid == txid && m.feeBump.targetText == text then
      ({ m with feeBump := { m.feeBump with reviewed := some (text, p), error := none } }, [])
    else (m, [])
  | .bumped g txid r =>
    if !m.sameWallet g then ({ m with spendingInFlight := false }, []) else
    let g := m.generation
    if m.feeBump.txid != txid then ({ m with spendingInFlight := false }, [.refresh g]) else
    ({ m with feeBump := { m.feeBump with replacement := some r, bumping := false }, spendingInFlight := false }, [.refresh g])
  | .catalogStored g stored =>
    if current g then ({ m with settingsDraft := { m.settingsDraft with catalog := some stored } }, []) else (m, [])
  | .peers g ps => if current g then ({ m with settingsDraft := { m.settingsDraft with peers := ps } }, []) else (m, [])
  | .peersReset g =>
    if !m.sameWallet g then (m, []) else
    let g := m.generation
    ({ m with settingsDraft := { m.settingsDraft with resettingPeers := false } }, [.connectedPeers g, .refresh g])
  | .exported g e file =>
    if sensitive g e && m.hasSheet .exportBundle then
      ({ m with exportState := { m.exportState with file := some file, busy := false, error := none } }, [])
    else (m, [.removeExport file])
  | .revealed g e words =>
    if sensitive g e then ({ m with reveal := { words } }.present .revealPhrase, [])
    else (m, [])
  | .card g name card =>
    if current g && m.settings.ownDisplayName.trimAscii.copy == name then ({ m with shareCard := { card := some card } }, []) else (m, [])
  | .pasteParsed g text r =>
    if !current g || m.person.pasted != text then (m, []) else
    match r with
    | .ok p => ({ m with person := { m.person with parsed := some p, error := none } }, [])
    | .error e => ({ m with person := { m.person with parsed := none, error := some e } }, [])
  | .senderLookup g txid source addresses =>
    if current g && m.person.mode.txid == some txid then
      ({ m with person := { m.person with inferring := false, inferredAddresses := addresses, inferredSource := some source } }, [])
    else (m, [])
  | .pasted target text =>
    match target with
    | .destination =>
      m.editSend fun i => { i with destination := text.trimAscii.copy }
    | .person => m.setPersonPasted text
    | .importBundle => ({ m with onboarding := { m.onboarding with importText := text } }, [])
    | .multisigDescriptor => stepMultisig (.setDescriptor text) m
    | .memberKeys =>
      -- SignerPickerSheet's `paste()`: one key, or several that always sign together
      let b := m.multisigBuild
      let keys := signerKeysOf text
      if keys.isEmpty then ({ m with multisigBuild := { b with pasteError := some "The clipboard holds no key." } }, []) else
      match signerKeysError text m.settings.network with
      | some e => ({ m with multisigBuild := { b with pasteError := some e } }, [])
      | none =>
        let labelled := keys.map fun k => ({ key := k, label := "Pasted " ++ keyFingerprint k m.settings.network } : BuildKey)
        let f := b.addPick labelled none none b.pickInto
        { m with multisigBuild := { f with pasteError := none }.clamp m.settings.network }.closeSheet .signerPicker
    | .multisigRecoveryKey =>
      ({ m with multisigBuild := { m.multisigBuild with recoveryKey := Winnow.Keys.Unicode.trimWhitespace text }.clamp m.settings.network }, [])
    | .multisigPSBT => ({ m with collect := { m.collect with pasted := text } }, [])
    | .accountPSBT id =>
      -- the account page's paste: filed as the draft at once, then the collection step opens
      if m.collect.busy then (m, []) else
      if text.trimAscii.isEmpty then ({ m with collect := { m.collect with error := some "The clipboard holds no PSBT." } }, []) else
      let (m', e) := m.runCollect
      (m', [.adoptDraft m.generation e id text])
    | .signerKeys => ({ m with signerKeys := { m.signerKeys with text := text, error := none } }, [])
  | .multisig .. | .multisigChecked .. | .multisigAdded .. | .multisigCreated .. | .multisigRemoved ..
  | .drafted .. | .collected .. | .draftBroadcast .. | .spendHandled .. | .ledgerPaired ..
  | .ledgerAddressShown .. | .ledgerRegistered .. =>
    m.onMultisigHost h
  | .signerSaved .. | .signerRenamed .. | .signerRemoved .. => m.onSignerHost h
  | .copiedExpired key => if m.copied == some key then ({ m with copied := none }, []) else (m, [])
  | .deleted g =>
    if !current g then (m, []) else
    let m' := m.nextWallet
    let m' := { m' with stage := Stage.onboarding, walletID := none, status := ({} : Status), records := ({} : Records),
                        multisig := ({} : MultisigOverview), collect := m'.collect.cleared }
    let m' := { m' with phase := SyncPhase.idle, confirm := none, sheets := [], routes := [], tabRoutes := [], tab := 0 }
    (m', [.stopNetworking])
  | .captured on => ({ m with captured := on }, [])
  | .backgroundRefresh available => ({ m with backgroundRefreshAvailable := available }, [])
  | .bgtask id kind =>
    -- `handle(_:)`: ask for the next checks first; a task launched before the wallet opened waits for boot
    if m.stage == .loading then ({ m with pendingBackgroundTask := some (id, kind) }, [.scheduleBackgroundTasks])
    else (m, [.scheduleBackgroundTasks, .runBackgroundTask id kind m.settings])
  | .bgtaskExpired id _ =>
    if m.pendingBackgroundTask.any (·.1 == id) then ({ m with pendingBackgroundTask := none }, [.expireBackgroundTask id])
    else (m, [.expireBackgroundTask id])
  | .scene active =>
    -- `scenePhaseChanged` journals the phase before acting on it
    let phase : Cmd := .journal "app.scenePhase" [("phase", if active then "active" else "background")]
    if active then
      let m := { m with active := true }
      -- the Send tab's rate in flight was dropped with the old generation
      let rate := if m.settings.advancedMode && m.tab == 1 then [.resolveRate m.generation m.sendInputs m.status.feeFloorMilli] else []
      let resume := if m.stage == .ready then [.startNetworking m.generation m.settings, .refresh m.generation] ++ rate
        else if m.stage == .onboarding && m.walletID.isNone then [.startNetworking m.generation m.settings, .discoverCloud]
        else if m.stage == .onboarding then [.startNetworking m.generation m.settings] else []
      let window := if m.hasSheet .receive && !m.receive.address.isEmpty then [.watchAddress m.generation m.receive.address] else []
      (m, [phase, .cloudScene true] ++ resume ++ window ++ [.backgroundRefreshStatus])
    else
      let (m, cs) := m.background
      (m, phase :: cs)
  | .sceneInactive => (m, [.journal "app.scenePhase" [("phase", "inactive")]])

/-- Switch to the other network's wallet (`switchNetwork`): a new generation, nothing carried over. -/
def Model.switchNetwork (m : Model) (net : Network) : Model × List Cmd :=
  if net == m.settings.network then (m, []) else
  -- a test session locked to one network stays there
  if m.forcedNetwork.any (· != net) then (m, []) else
  let s := { m.settings with network := net }
  let m0 := m.nextWallet
  let m' := { m0 with settings := s, stage := Stage.loading, status := ({} : Status), records := ({} : Records),
                      multisig := ({} : MultisigOverview), collect := m0.collect.cleared,
                      phase := SyncPhase.idle, walletID := none, routes := [], tabRoutes := [], sheets := [], confirm := none,
                      send := ({} : SendState), tab := 0 }
  (m', [.stopNetworking, .stopWatchingAddress, .saveSettings s, .openWallet m'.generation net false])

def step (msg : Msg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  match msg with
  | .createWallet =>
    ({ m with onboarding := { m.onboarding with busy := true, error := none } }, [.createWallet g m.settings.network])
  | .openImport => ({ m with onboarding := { m.onboarding with importReport := none, error := none } }.present .importWallet, [])
  | .setImportText s => ({ m with onboarding := { m.onboarding with importText := s } }, [])
  | .pasteImport => (m, [.paste .importBundle])
  | .importWallet =>
    ({ m with onboarding := { m.onboarding with busy := true, error := none } },
     [.importWallet g m.settings.network m.onboarding.importText])
  | .finishOnboarding =>
    if m.walletID.isNone then (m, []) else
    ({ m with stage := .ready, sheets := [], onboarding := ({} : Onboarding) },
     [.finishOnboarding g, .refresh g, .startNetworking g m.settings])
  | .closeSheet => m.closeTop
  | .setNetwork i =>
    match networks[i]? with
    | some net => m.switchNetwork net
    | none => (m, [])
  | .switchNetwork net => m.switchNetwork net
  | .askAdvanced => ({ m with confirm := some .advancedMode }, [])
  | .setAdvanced b =>
    if b == m.settings.advancedMode then ({ m with confirm := none }, []) else
    let s := { m.settings with advancedMode := b }
    -- the Settings tab is a new view: its staged gateway edits start again from the saved settings
    let m := { m with settingsDraft := { m.settingsDraft with gatewaysLoaded := false, gatewayError := none } }
    ({ m with settings := s, confirm := none, tab := 0, routes := [], tabRoutes := [] }.loadGatewayDraft,
     [.saveSettings s, .journal "setting.advancedMode" [("enabled", toString b)]])
  | .dismissConfirm => ({ m with confirm := none }, [])
  | .selectTab i =>
    -- each tab keeps its own navigation stack
    let m' := m.switchTab i
    (m', if i == 2 then m'.settingsAppear else if i == 1 then [.resolveRate g m.sendInputs m.status.feeFloorMilli] else [])
  | .openReceive => ({ m with receive := ({} : Receive) }.present .receive, [.receiveAddress g false])
  | .openSend =>
    let m := { m with send := { inputs := { network := m.settings.network } } }.present .send
    (m, [.resolveRate g m.sendInputs m.status.feeFloorMilli])
  | .copy key t => ({ m with copied := some key }, [.copy t .interchange, .timer 2000 (.copiedExpired key)])
  | .openExplorer url exposed => ({ m with confirm := some (.openExternal url exposed) }, [])
  | .openURL url => ({ m with confirm := none }, [.openURL url])
  | .setExpanded key b =>
    ({ m with expanded := if b then (if m.expanded.contains key then m.expanded else m.expanded ++ [key]) else m.expanded.erase key }, [])
  | .syncNow => (m, [.syncNow g])
  | .retryPeers => (m, [.retryPeers g])
  | .retryOpen => ({ m with stage := .loading }, [.openWallet g m.settings.network true])
  | .send s => stepSend s m
  | .receive r => stepReceive r m
  | .home h => stepHome h m
  | .settings s => stepSettings s m
  | .backup b => stepBackup b m
  | .people p => stepPeople p m
  | .multisig mm => stepMultisig mm m
  | .signer sm => stepSigner sm m
  | .cloud cm => stepCloud cm m
  | .host h => onHost h m

/-- The shell's system events: background tasks launched and expired, scene phase as `scenePhaseChanged` reads it (`active` activates,
`background` suspends; `inactive` is still foreground: a system prompt such as Face ID or paste must
neither stop syncing nor discard the result it is waiting for) and screen capture. The privacy cover
over an inactive scene is the shell's. -/
def system (j : Lean.Json) : Option Host :=
  let task (key : String) : Option (String × String) := do
    let t ← (j.getObjVal? key).toOption
    let id ← (t.getObjValAs? String "id").toOption
    return (id, (t.getObjValAs? String "kind").toOption.getD "refresh")
  match j.getObjValAs? String "scene", j.getObjValAs? Bool "captured", task "bgtask", task "bgtaskExpired" with
  | .ok "active", _, _, _ => some (.scene true)
  | .ok "background", _, _, _ => some (.scene false)
  | .ok "inactive", _, _, _ => some .sceneInactive
  | .ok _, _, _, _ => none
  | _, .ok on, _, _ => some (.captured on)
  -- background tasks: launched (`{"bgtask":{"id","kind"}}`) and expired (`{"bgtaskExpired":…}`)
  | _, _, some (id, kind), _ => some (.bgtask id kind)
  | _, _, _, some (id, kind) => some (.bgtaskExpired id kind)
  | _, _, _, _ => none

def update (msg : Msg) (m : Model) : Model := (step msg m).1
def cmds (msg : Msg) (m : Model) : List Cmd := (step msg m).2

end WinnowApp
