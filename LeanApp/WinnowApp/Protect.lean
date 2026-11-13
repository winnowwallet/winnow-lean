import WinnowApp.Multisig
import WinnowApp.Signers
import WinnowApp.Ids

/-! More protection as the balance grows, and a Ledger found nearby.

* The home's two balance cards (`Pure.lean`'s thresholds): at `hardwareWalletThresholdSats` with no Ledger
  paired, "This is more than a phone should hold alone", which opens the Ledger setup below; at
  `multipartyThresholdSats` with no multi-party account, "Large amounts invite wrench attacks", which opens
  the builder for other people's keys. Each is dismissed for good (the settings remember it); below the
  thresholds both live only in Settings → Security.
* The nearby card: while the app is open and no Ledger is paired, the home scans for the Ledger services
  (`ble.scan`, which connects to nothing) once it appears and every 30 s. A Nano in range presents a
  medium sheet, like AirPods pairing; Not now is remembered per device identifier.
* Its Set up chains the existing flows: `pairLedger` → `createMultisigAccount` (this phone + the Ledger,
  2-of-2, or 2-of-3 with a recovery key; creating registers the account on the paired Ledger) →
  `registerLedger` when that registration did not happen → `verifyLedgerAddress`, so the person sees the
  first receive address on the Ledger and on the phone. "Verify" is the registered wallet policy and that
  on-device address check; Ledger's genuine-device attestation needs Ledger's servers and is out of scope.
* Onboarding's last card asks for Bluetooth (`ble.state`, which makes iOS ask), once. Declining changes
  nothing else. -/

namespace WinnowApp
open LeanNative

/-- The headline: the wallet's and the accounts' coins together. -/
def totalBalance (m : Model) : Int := m.status.balance + m.status.accountsBalance

/-- An account with a key that is neither this phone's nor a paired Ledger's: someone else holds one. -/
def Model.hasMultipartyAccount (m : Model) : Bool :=
  let mine := m.multisig.keyExpression.toList ++ m.multisig.ledgers.flatMap (·.keys)
  m.multisig.accounts.any fun a => a.signerExpressions.any (!mine.contains ·)

def Model.showsHardwareCard (m : Model) : Bool :=
  m.stage == .ready && totalBalance m ≥ hardwareWalletThresholdSats && m.multisig.ledgers.isEmpty &&
    !m.settings.hardwareCardDismissed

def Model.showsMultipartyCard (m : Model) : Bool :=
  m.stage == .ready && totalBalance m ≥ multipartyThresholdSats && !m.hasMultipartyAccount &&
    !m.settings.multipartyCardDismissed

/-- "Nano X 1A2B" → "Ledger Nano X": the model without the advertisement's id suffix. -/
def ledgerTitle (name : String) : String :=
  let words := name.splitOn " "
  let words := match words.getLast? with
    | some w => if words.length > 1 && w.length == 4 && w.all (fun c => c.isDigit || ('A' ≤ c && c ≤ 'F')) then words.dropLast else words
    | none => words
  let model := " ".intercalate words
  if model.startsWith "Ledger" then model else s!"Ledger {model}"

/-! ## The scan -/

/-- Whether a scan may offer the card now: the home showing with nothing over it, the app in front, no Ledger
paired and no setup running. -/
def Model.wantsLedgerScan (m : Model) : Bool :=
  m.stage == .ready && m.active && m.multisig.ledgers.isEmpty && m.routes.isEmpty && m.sheets.isEmpty &&
    m.confirm.isNone && m.ledgerSetup.isNone

/-- Start this generation's 30 s scan (once per generation: a background trip ends the chain, and coming back
starts the next). The first tick waits 2 s, so the accounts and signers are known first. -/
def Model.startLedgerScan (m : Model) : Model × List Cmd :=
  if m.ledgerScanGen == some m.generation then (m, []) else
  ({ m with ledgerScanGen := some m.generation }, [.timer 2000 (.ledgerScanDue m.generation true)])

/-- A tick: scan when the card may show, and (`again`) the next tick in 30 s. -/
def Model.onLedgerScanDue (m : Model) (g : Nat) (again : Bool) : Model × List Cmd :=
  if g != m.generation then (m, []) else
  (m, (if m.wantsLedgerScan then [.scanLedgers g] else []) ++ (if again then [.timer 30000 (.ledgerScanDue g true)] else []))

/-- The Ledgers seen: the first one not answered Not now presents the card. -/
def Model.onLedgersNearby (m : Model) (g : Nat) (seen : List NearbyLedger) : Model × List Cmd :=
  if g != m.generation || !m.wantsLedgerScan then (m, []) else
  match seen.find? (fun l => !m.settings.ledgersNotNow.contains l.id) with
  | some l => ({ m with nearbyLedger := some l, ledgerSetup := none }.present .ledgerNearby,
               [.journal "ledger.nearby" [("name", l.name)]])
  | none => (m, [])

/-- Onboarding is over: the Bluetooth card the first time, then the scan. -/
def Model.endOnboarding (m : Model) : Model × List Cmd :=
  if m.settings.bluetoothIntroShown then m.startLedgerScan else
  let s := { m.settings with bluetoothIntroShown := true }
  let (m, scan) := ({ m with settings := s }.present .bluetoothIntro).startLedgerScan
  (m, [.saveSettings s] ++ scan)

/-! ## Set up -/

def ledgerSetupAccountName : String := "Ledger vault"

/-- The members of the account Set up creates: this phone, the Ledger, and the recovery key when asked. -/
def Model.setupMembers (m : Model) (ledger : SignerInfo) (s : LedgerSetup) : List (List String × Option Nat) :=
  (m.multisig.keyExpression.toList.map fun k => ([k], none)) ++ [(ledger.keys, none)] ++
  (if s.withRecoveryKey then [([s.recoveryKey], none)] else [])

/-- The step's command, from where the setup is (also Try again after a failure). -/
def Model.runSetup (m : Model) (s : LedgerSetup) : Model × List Cmd :=
  let g := m.generation
  let s := { s with error := none }
  let name := (m.nearbyLedger.map (·.name)).getD "Nano X"
  match s.step with
  | .choose | .pairing =>
    -- a Ledger paired already (pairing done, the account not yet made) goes straight to the account
    match m.multisig.ledgers.head? with
    | some l => ({ m with ledgerSetup := some { s with step := .creating l.id }, multisigBuild := { m.multisigBuild with creating := true } },
                 [.createMultisigAccount g ledgerSetupAccountName 2 (m.setupMembers l s) none])
    | none => ({ m with ledgerSetup := some { s with step := .pairing } }, [.pairLedger g name])
  | .creating sid =>
    match m.signer? sid with
    | some l => ({ m with ledgerSetup := some s, multisigBuild := { m.multisigBuild with creating := true } },
                 [.createMultisigAccount g ledgerSetupAccountName 2 (m.setupMembers l s) none])
    | none => ({ m with ledgerSetup := some s }, [.multisigOverview g])
  | .registering id => ({ m with ledgerSetup := some s, ledgerRegistering := some id }, [.registerLedger g id])
  | .verifying id =>
    let index := ((m.multisigInfo? id).map (·.nextReceiveIndex)).getD 0
    ({ m with ledgerSetup := some s, ledgerVerify := { id, index, checking := true } }, [.verifyLedgerAddress g id index])
  | .done _ => (m, [])

/-- Coming back from the background: an overview the setup was waiting for belonged to the old generation and
was dropped, so ask again (every other step's answer is taken from any generation of this wallet). -/
def Model.resumeLedgerSetup (m : Model) : List Cmd :=
  match m.ledgerSetup with
  | some { step := .creating _, error := none, .. } => if m.multisigBuild.creating then [] else [.multisigOverview m.generation]
  | _ => []

/-- Whether the setup is waiting on the Ledger or the backend (the sheet cannot be closed then). -/
def LedgerSetup.busy (s : LedgerSetup) : Bool :=
  s.error.isNone && match s.step with | .choose | .done _ => false | _ => true

/-- The backend's answers move the setup on (after `onMultisigHost` has handled them as it always does). -/
def Model.advanceSetup (m : Model) (h : Host) : Model × List Cmd :=
  match m.ledgerSetup with
  | none => (m, [])
  | some s =>
    let g := m.generation
    let failWith (e : String) : Model × List Cmd := ({ m with ledgerSetup := some { s with error := some e } }, [])
    match h, s.step with
    | .ledgerPaired g' sid, .pairing =>
      if !m.sameWallet g' then (m, []) else
      -- the overview `onMultisigHost` asked for brings the Ledger's keys
      ({ m with ledgerSetup := some { s with step := .creating sid } }, [])
    | .multisig g' _, .creating sid =>
      -- any generation of this wallet: a trip to the background mid-setup must not strand it
      if !m.sameWallet g' || s.error.isSome then (m, []) else
      match m.signer? sid with
      | some l =>
        if l.keys.isEmpty then (m, []) else
        -- once: the account's answer moves the step on
        if m.multisigBuild.creating then (m, []) else
        ({ m with multisigBuild := { m.multisigBuild with creating := true } },
         [.createMultisigAccount g ledgerSetupAccountName 2 (m.setupMembers l s) none])
      | none => (m, [])
    | .multisigCreated g' id _ registration, .creating _ =>
      if !m.sameWallet g' then (m, []) else
      let m := { m with multisigBuild := { m.multisigBuild with creating := false } }
      match registration with
      | some (.ok _) => m.runSetup { s with step := .verifying id }
      | some (.error e) => ({ m with ledgerSetup := some { s with step := .registering id, error := some e } }, [])
      | none => m.runSetup { s with step := .registering id }
    | .ledgerRegistered g' id r, .registering id' =>
      if !m.sameWallet g' || id != id' then (m, []) else
      match r with
      | .ok () => m.runSetup { s with step := .verifying id }
      | .error e => failWith e
    | .ledgerAddressShown g' id _ r, .verifying id' =>
      if !m.sameWallet g' || id != id' then (m, []) else
      match r with
      | .ok address => ({ m with ledgerSetup := some { s with step := .done id, address := some address, error := none } }, [])
      | .error e => failWith e
    | .failed g' ctx e, step =>
      if !m.sameWallet g' then (m, []) else
      match ctx, step with
      | "ledgerPair", .pairing => failWith e
      | "multisigBuild", .creating _ =>
        ({ m with ledgerSetup := some { s with error := some e }, multisigBuild := { m.multisigBuild with creating := false } }, [])
      | _, _ => (m, [])
    | _, _ => (m, [])

/-- The nearby card, its Set up, and onboarding's Bluetooth card. -/
def stepLedgerCard (msg : LedgerCardMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  match msg with
  | .setUp => ({ m with ledgerSetup := some {} }, [])
  | .notNow =>
    let (m, cs) := m.closeSheet .ledgerNearby
    match m.nearbyLedger with
    | some l =>
      let s := { m.settings with ledgersNotNow := if m.settings.ledgersNotNow.contains l.id then m.settings.ledgersNotNow
                                                 else m.settings.ledgersNotNow ++ [l.id] }
      ({ m with settings := s, nearbyLedger := none, ledgerSetup := none }, cs ++ [.saveSettings s])
    | none => ({ m with ledgerSetup := none }, cs)
  | .setWithRecoveryKey b =>
    match m.ledgerSetup with
    | some s => ({ m with ledgerSetup := some { s with withRecoveryKey := b, error := none } }, [])
    | none => (m, [])
  | .pasteRecoveryKey => (m, [.paste .setupRecoveryKey])
  | .start =>
    match m.ledgerSetup with
    | none => (m, [])
    | some s =>
      if s.busy then (m, []) else
      if s.step == .choose && s.withRecoveryKey then
        match (if s.recoveryKey.isEmpty then some "Paste the recovery key first." else signerKeysError s.recoveryKey m.settings.network) with
        | some e => ({ m with ledgerSetup := some { s with error := some e } }, [])
        | none => m.runSetup s
      else m.runSetup s
  | .addressesMatch =>
    match m.ledgerSetup with
    | some { step := .done id, .. } =>
      let (m, cs) := { m with ledgerSetup := none, nearbyLedger := none }.closeSheet .ledgerNearby
      let (m, cs2) := stepMultisig (.openAccount id) { m with routes := [] }
      (m, cs ++ cs2 ++ [.journal "ledger.setup" [("account", id)]])
    | _ => (m, [])
  | .allowBluetooth =>
    let (m, cs) := m.closeSheet .bluetoothIntro
    (m, cs ++ [.askBluetooth, .timer 1500 (.ledgerScanDue g false)])
  | .skipBluetooth => m.closeSheet .bluetoothIntro

/-! ## Views -/

/-- The balance cards the home shows (records-test's `balanceCards`). -/
def protectionCards (m : Model) : List H :=
  let card (id title text action : String) (msg : Msg) (dismissID : String) (hardware : Bool) : H :=
    .identified id (.section "" ""
      [ .row [Html.tone .warning (.icon (if hardware then "lock.shield" else "person.3")), .text title .headline]
      , caption text
      , .button action .primary (some msg)
      , .identified dismissID (.button "Don't show again" .plain (some (.home (.dismissCard hardware)))) ])
  (if m.showsHardwareCard then
    [card Ids.hardwareWalletCard "This is more than a phone should hold alone"
      "A phone can be lost, stolen or broken into. A Ledger keeps a second key off the phone, so a payment needs both."
      "Protect it with a Ledger" (.home .protectWithLedger) Ids.dismissHardwareCard true] else []) ++
  (if m.showsMultipartyCard then
    [card Ids.multipartyCard "Large amounts invite wrench attacks"
      "When no one person can move the money, threatening one person gets nothing. Share the signing with people you trust."
      "Build an account with other people's keys" (.home .buildWithOthers) Ids.dismissMultipartyCard false] else [])

/-- The nearby card (a medium sheet) and its Set up. -/
def ledgerNearbySheet (m : Model) (inner : List H) : H :=
  let name := (m.nearbyLedger.map (·.name)).getD "Nano X"
  let title := ledgerTitle name
  let card := fun (cs : List H) => formSheet (if m.nearbyLedger.isSome then s!"{title} nearby" else "Protect with a Ledger")
    (if (m.ledgerSetup.map (·.busy)).getD false then none else some (.ledgerCard .notNow)) [] cs inner (size := .medium)
  match m.ledgerSetup with
  | none =>
    card
      [ .section "" ""
          [ .identified Ids.ledgerNearbyCard (.row [Html.tone .tint (.icon "lock.shield.fill"),
              .text (if m.nearbyLedger.isSome then s!"{title} nearby." else "Turn on your Ledger and open its Bitcoin app.") .headline])
          , body "Use it to protect this wallet: a payment then needs this phone and the Ledger, so a stolen phone alone cannot spend."
          , .identified Ids.ledgerSetUpButton (.button "Set up" .primary (some (.ledgerCard .setUp)))
          , .identified Ids.ledgerNotNowButton (.button "Not now" .plain (some (.ledgerCard .notNow))) ] ]
  | some s =>
    let progress (t : String) : List H := if s.error.isNone then [.progress t] else []
    let failure : List H :=
      match s.error with
      | some e => errorRows (some e) ++
        [ .identified Ids.ledgerSetupRetryButton (.button "Try again" .primary (some (.ledgerCard .start)))
        , .button "Not now" .plain (some (.ledgerCard .notNow)) ]
      | none => []
    card <| match s.step with
      | .choose =>
        [ .section "" (if s.withRecoveryKey then "Any two of this phone, the Ledger and the recovery key can spend. Keep the recovery key somewhere else." else "Every payment needs this phone and the Ledger.")
            ([ .identified Ids.ledgerSetupRecoveryToggle
                 (.toggle "Add a recovery key (2-of-3)" s.withRecoveryKey fun b => .ledgerCard (.setWithRecoveryKey b)) ] ++
             (if !s.withRecoveryKey then [] else
               if s.recoveryKey.isEmpty then [.button "Paste the recovery key" .plain (some (.ledgerCard .pasteRecoveryKey))]
               else [literal s.recoveryKey]) ++
             errorRows s.error ++
             [ .identified Ids.ledgerSetupStartButton (.button "Continue" .primary (some (.ledgerCard .start)))
             , .button "Not now" .plain (some (.ledgerCard .notNow)) ]) ]
      | .pairing => [.section "" "" (progress "Approve the pairing on the Ledger…" ++ failure)]
      | .creating _ => [.section "" "" (progress "Creating the account…" ++ failure)]
      | .registering _ => [.section "" "" (progress "Approve the account on the Ledger's screen…" ++ failure)]
      | .verifying _ => [.section "" "" (progress "Check the address on the Ledger's screen…" ++ failure)]
      | .done id =>
        let phone := ((m.multisigInfo? id).bind (·.receiveAddress)).orElse fun _ => s.address
        [ .section "" "The Ledger shows the account's first receive address. It must match this one, character for character."
            ([ .identified Ids.ledgerSetupDone (.text "Compare the addresses" .headline) ] ++
             (match phone with | some a => [.identified Ids.ledgerSetupAddress (literal a)] | none => []) ++
             [ .identified Ids.ledgerAddressesMatchButton (.button "They match" .primary (some (.ledgerCard .addressesMatch))) ]) ]

/-- Onboarding's last card: why Bluetooth, then the system's question. -/
def bluetoothIntroSheet (inner : List H) : H :=
  formSheet "Bluetooth" (some (.ledgerCard .skipBluetooth)) []
    [ .section "" "Winnow looks for a Ledger nearby only while it is open, and connects only when you set one up. Saying no changes nothing else."
        [ .identified Ids.bluetoothIntroCard (.row [Html.tone .tint (.icon "dot.radiowaves.left.and.right"),
            .text "Find your Ledger nearby" .headline])
        , body "With Bluetooth, Winnow can notice a Ledger in range and offer to protect this wallet with it."
        , .identified Ids.allowBluetoothButton (.button "Continue" .primary (some (.ledgerCard .allowBluetooth)))
        , .identified Ids.skipBluetoothButton (.button "Not now" .plain (some (.ledgerCard .skipBluetooth))) ] ]
    inner (size := .medium)

end WinnowApp
