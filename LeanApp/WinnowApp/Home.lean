import WinnowApp.Multisig
import WinnowApp.Protect
import WinnowApp.Settings
import WinnowApp.Backup
import WinnowApp.Payments
import WinnowApp.Ids

/-! The one home (BeginnerHomeView.swift, with HomeView.swift's accounts): the balance, the protection cards,
sync and activity, the accounts once one exists; HistoryRow,
PaymentDetailView (recipients, receive labels, sender, details, transaction) and FeeBumpView. -/

namespace WinnowApp
open LeanNative

/-! ## Update -/

def Model.currentPayment? (m : Model) : Option String :=
  match m.routes.getLast? with
  | some (.payment t) => some t
  | _ => none

/-- PaymentDetailView's `load()`: only a send whose transaction is not stored, once at a time, and not
while syncing (the `.task(id: syncing)` reruns it when a sync ends). -/
def Model.loadPayment (m : Model) : Model × List Cmd :=
  match m.currentPayment? with
  | none => (m, [])
  | some txid =>
    match m.payment? txid with
    | some row =>
      let h := row.item
      -- only the wallet's own sends: an account's entry carries its bytes
      if row.accountID.isNone && h.spent > 0 && h.outputs.isNone && !m.payment.loading && !m.status.syncing then
        ({ m with payment := { loading := true, error := none } }, [.loadPaymentDetails m.generation txid])
      else (m, [])
    | none => (m, [])

/-- Open AddPersonView in `mode`, with the paste field pre-filled. -/
def Model.openPerson (m : Model) (mode : PersonMode) (address : String) : Model × List Cmd :=
  let name := (mode.personID.bind m.person?).map (·.name) |>.getD ""
  let m' := { m with person := { mode, name, pasted := address } }.present .addPerson
  (m', if address.trimAscii.isEmpty then [] else [.parsePaste m.generation address])

/-- A fresh Send form addressed to a saved person (SendView's `consumeRequestedPerson`). -/
def Model.sendTo (m : Model) (personID : Option String) : Model × List Cmd :=
  let p := personID.bind m.person?
  let inputs : SendInputs := { network := m.settings.network, walletID := m.walletID,
                               personID := p.map (·.id), paymentIndex := p.map (·.nextPaymentIndex) }
  let m := { m with send := { inputs } }
  let m := if m.hasSheet .send then m else m.present .send
  (m, [.resolveRate m.generation inputs m.status.feeFloorMilli])

/-- Home and the payment screen (records-test's `homeScreens`). -/
def stepHome (msg : HomeMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  match msg with
  | .openPayment txid => { m with routes := m.routes ++ [Route.payment txid], payment := {}, expanded := [] }.loadPayment
  | .openBackup => ({ m with routes := m.routes ++ [Route.backup] }, [])
  | .openSettings => ({ m with routes := m.routes ++ [Route.settings] }, [])
  | .openNetwork page =>
    -- the peers screen loads the connected peers and the census line, and its staged routing edits
    let m := { m with routes := m.routes ++ [Route.network page] }
    if page == .peers then (m.loadGatewayDraft, m.settingsAppear) else (m, [])
  | .openMultisigAccounts => ({ m with routes := m.routes ++ [Route.multisigAccounts] }, [.multisigOverview g])
  | .explainWarning kind => ({ m with confirm := some (.homeWarning kind) }, [])
  | .warningSettings kind =>
    -- Settings, then the page (as `openNetwork` opens it): Back leads through Settings to the home
    let page : NetworkPage := if kind == .network then .sync else .peers
    let m := { m with confirm := none, routes := m.routes ++ [Route.settings, Route.network page] }
    if page == .peers then (m.loadGatewayDraft, m.settingsAppear) else (m, [])
  | .dismissCard hardware =>
    let s := if hardware then { m.settings with hardwareCardDismissed := true } else { m.settings with multipartyCardDismissed := true }
    ({ m with settings := s }, [.saveSettings s, .journal "card.dismissed" [("card", if hardware then "hardwareWallet" else "multiparty")]])
  | .protectWithLedger =>
    -- the nearby card's setup, whether or not a Ledger is advertising now (pairing finds it)
    ({ m with ledgerSetup := none }.present .ledgerNearby, [])
  | .buildWithOthers => stepMultisig .openBuild { m with routes := [] }
  | .pop => ({ m with routes := m.routes.dropLast, payment := {}, expanded := [] }, [])
  | .loadPayment => m.loadPayment
  | .editRecipient address pid => m.openPerson { personID := pid } address
  | .removeRecipient pid => (m, [.updateRecipient g pid none false "payment"])
  | .editPaymentLabel address =>
    let draft := (lookup m.records.receiveLabels address).getD ""
    ({ m with labelEditor := { address, draft } }.present .labelEditor, [])
  | .labelSender => match m.currentPayment? with
    | some t => m.openPerson { txid := some t } ""
    | none => (m, [])
  | .attachSenderDestination pid => match m.currentPayment? with
    | some t => m.openPerson { personID := some pid, txid := some t } ""
    | none => (m, [])
  | .removeSenderLabel => match m.currentPayment? with
    | some t => (m, [.removeSenderLabel g t])
    | none => (m, [])
  | .sendToPerson pid => m.sendTo (some pid)
  | .openFeeBump => match m.currentPayment? with
    | some t => ({ m with feeBump := { txid := t } }.present .feeBump, [.pendingFeeRate g t])
    | none => (m, [])
  | .setBumpRate s =>
    if m.feeBump.replacement.isSome then (m, []) else
    ({ m with feeBump := { m.feeBump with targetText := s, reviewed := none, error := none } }, [])
  | .reviewBump =>
    match parseRateMilli m.feeBump.targetText (trimNewlines := true) with
    | some milli =>
      ({ m with feeBump := { m.feeBump with reviewed := none, error := none } },
       [.previewFeeBump g m.feeBump.txid m.feeBump.targetText milli])
    | none => (m, [])
  | .bump =>
    match m.feeBump.reviewed with
    | some (_, p) =>
      if m.feeBump.bumping then (m, [])
      else if m.spendingInFlight then
        (m.fail "feeBump" "Another payment is already being signed and broadcast. Wait for it to finish.", [])
      else ({ m with feeBump := { m.feeBump with bumping := true, error := none }, spendingInFlight := true },
            [.bumpFee g m.feeBump.txid p])
    | none => (m, [])

/-! ## View -/

/-- A payment's net amount: green in, red out. -/
def amountText (net : Int) : H :=
  Html.tone (if net > 0 then .positive else if net < 0 then .negative else .standard) (body (signedSatsText net))

/-- `HistoryRow`: who, the labels, the net amount, and Confirmed/Pending/Replaced (the block, fee and
replacement are on the payment screen). The title opens the payment. The row, and its status lines. -/
def historyRow (m : Model) (h : HistoryItem) (tappable := true) : H × List H :=
  let labels := historyLabels m.records h
  let title := historyTitle m.records h
  let status : List H :=
    [.identified (Ids.historyStatus h.txid)
      (caption (if h.replacedBy.isSome then "Replaced" else if h.height > 0 then "Confirmed" else "Pending"))]
  (.row [ .col ([.identified (Ids.historyPayment (h.txid))
                  (if tappable then navLink title (some (.home (.openPayment h.txid))) else body title)] ++
               (if labels.isEmpty then [] else [caption labels]))
       , .spacer
       , .col ([amountText h.net] ++ status) ], status)

/-- `HistoryRow`'s title for a row: an account's payment as the wallet's, a draft as awaiting signatures,
a move between the wallet and an account as such. -/
def paymentTitle (m : Model) (p : DisplayedPayment) : String :=
  match p.source with
  | .wallet | .account _ => historyTitle m.records p.item
  | .draft name _ => s!"Awaiting signatures · {name}"
  | .transfer f t _ =>
    if f == walletName then s!"Moved to {t}" else if t == walletName then s!"Moved from {f}" else s!"Moved from {f} to {t}"

/-- `HistoryRow` and `PaymentLink`: an arrow for the direction, who (and which account), the labels, the
amount, and Confirmed/Pending/Replaced; a draft says how many signatures it has. A draft opens its collection
step and anything else the payment. -/
def paymentRow (m : Model) (p : DisplayedPayment) (tappable := true) : H :=
  let h := p.item
  let labels := historyLabels m.records h
  let title := paymentTitle m p
  let action : Option Msg :=
    if !tappable then none
    else match p.source, p.accountID with
      | .draft .., some id => some (.multisig (.openPSBT id))
      | .draft .., none => none
      | _, _ => some (.home (.openPayment h.txid))
  let rowID := if p.isDraft then (Ids.historyDraft (p.accountID.getD "")) else (Ids.historyPayment (h.txid))
  let status : List H :=
    match p.source with
    | .draft _ signatures =>
      [.identified (Ids.transactionDraft (h.txid))
        (caption s!"{signatures} signed · tap to continue")]
    | _ => (historyRow m h).2
  let amount : H := match p.source with
    | .transfer _ _ moved => body s!"{groupDigits moved} sats"
    | _ => amountText h.net
  -- an arrow for the direction, who and the status under each other, the amount alone. The arrow is its own
  -- icon beside the texts (it keeps its size; the texts wrap), not a symbol inside the title: drawn inside it,
  -- a title above an account's name and a status was squeezed to a few letters
  let arrow := if h.net > 0 then "arrow.down.left" else if h.net < 0 then "arrow.up.right" else "arrow.left.arrow.right"
  .row [ .icon arrow
       , .col ([.identified rowID (match action with
                  | some a => navLink title (some a)
                  | none => body title)] ++
               (match p.source with
                | .account name => [.identified (Ids.paymentAccount (h.txid)) (caption name)]
                | _ => []) ++
               (if labels.isEmpty then [] else [caption labels]) ++ status)
       , .spacer
       , amount ]

/-- A warning the home keeps to one short line: a filled symbol and a few words in the warning colour,
tapped for the whole message in an alert, which leads on to the Settings page with the details and Retry. -/
def compactWarning (id label : String) (kind : HomeWarning) (symbol := "exclamationmark.triangle.fill")
    (tone : LeanNative.Tone := .warning) : H :=
  .identified id (Html.decor { tone, symbol } (.button label .plain (some (.home (.explainWarning kind)))))

/-- The home's network problem, in a few words: no peer can be reached, or syncing keeps failing (a dropped
peer or two stays quiet: `simpleSyncError`). -/
def networkWarningLabel (m : Model) : Option String :=
  if m.phase.summary m.status.syncing == .peersUnavailable then some "Offline"
  else if (simpleSyncError m.status.lastSyncError m.status.transientSyncError m.status.transientSyncFailures).isSome then
    some "Sync problem"
  else none

/-- The network alert's message: the error itself, as Settings → Network → Sync shows it. -/
def networkWarningMessage (m : Model) : String :=
  match simpleSyncError m.status.lastSyncError m.status.transientSyncError m.status.transientSyncFailures, m.status.lastSyncError with
  | some e, _ => e
  | none, some e => e
  | none, none => (syncStatusText m.phase).getD "Check your connection."

def syncLine (m : Model) : H :=
  match m.phase.summary m.status.syncing with
  | .synced => .row [Html.tone .positive (.icon "checkmark.circle"), .identified Ids.syncSummaryText (caption "Up to date")]
  | .peersUnavailable => compactWarning Ids.homeNetworkWarning "Offline" .network
  | .syncing => .identified Ids.syncSummaryText (.progress "Syncing…")

/-- `AccountsBalanceLine`: how much of the headline sits in multisig accounts, which need co-signers to move;
nothing when the phone has no account. -/
def accountsBalanceLine (m : Model) : List H :=
  let count := m.multisig.accounts.length
  if count == 0 then [] else
  [.identified Ids.accountsBalanceText
    (caption s!"of which {satsText m.status.accountsBalance} in {count} multisig account{if count == 1 then "" else "s"}, needs co-signers")]

/-- `PeerRoutingBanner`: the home's routing line (a lock when every peer is behind Tor or I2P; a short warning
when any peer can see the phone's IP address, its whole message in an alert). -/
def peerRoutingBanner (m : Model) : H :=
  let state := PeerRoutingState.current m.settings.peerGatewaySettings.mode m.status.activeGateways m.status.discoveringGateways
  if state.warns then
    compactWarning Ids.peerRoutingBanner state.shortLabel .routing state.symbol (if state == .offline then .negative else .warning)
  else .identified Ids.peerRoutingBanner (.row [.icon state.symbol, caption state.message])

/-- The headline balance: the largest type in the app. -/
def balanceText (m : Model) : H := .identified Ids.balanceText (.text (satsText (totalBalance m)) .largeTitle)

/-- The balance card: one cell, the amount large, then its status line and the network's badge. -/
def balanceSection (m : Model) : H :=
  .section "" "" [.col ([ caption "Balance", balanceText m ] ++
                  accountsBalanceLine m ++ [
                    .row ([syncLine m] ++ (if m.settings.network == .mainnet then [] else
                      [.spacer, .identified Ids.networkTag (Html.badge (Html.tone .warning (caption s!"{m.settings.network.label} · test coins")))])) ] ++
                  -- syncing keeps failing while peers answer: the same short warning under the status (Offline
                  -- is the status line itself); the error and Retry are in Settings → Network → Sync
                  (match networkWarningLabel m with
                   | some label => if m.phase.summary m.status.syncing == .peersUnavailable then []
                                   else [compactWarning Ids.homeNetworkWarning label .network]
                   | none => []) ++
                  (if m.settings.network == .mainnet then [peerRoutingBanner m] else []))]

def activitySection (m : Model) : H :=
  .section "Activity" ""
    (if m.status.payments.isEmpty then [caption "Nothing yet. Payments appear here once they are confirmed."]
     else m.status.payments.map (paymentRow m))

/-- The home's Accounts, once this phone has a multisig account. -/
def accountsSection (m : Model) : List H :=
  if m.multisig.accounts.isEmpty then [] else
  [.identified Ids.homeAccountsSection (.section "Accounts" ""
    (m.multisig.accounts.map fun a =>
      .row [.identified (Ids.multisigAccount (a.id)) (navLink a.name (some (.multisig (.openAccount a.id))) (symbol := "person.3")), .spacer,
            Html.tone .secondary (body (satsText a.balance))]))]

def homeSections (m : Model) : List H :=
  [ balanceSection m ] ++ protectionCards m ++
  [ .section "" "" [.row [.identified Ids.receiveButton (Html.symbol "arrow.down.left" (.button "Receive" .plain (some .openReceive))),
                          .identified Ids.openSendButton (Html.symbol "arrow.up.right" (.button "Send" .primary (some .openSend)))]] ] ++
  accountsSection m ++
  [ activitySection m
  , beginnerBackupSection m ]

/-- `ChainCheckStatus`: when a scan last reached the tip, and whether iOS may check in the background
(background checks are requests; iOS decides when they run). -/
def chainCheckStatus (m : Model) : List H :=
  [ .identified Ids.lastCompleteChainCheck (caption (match m.status.lastCheckedAgo with
      | some ago => s!"Chain last checked {ago} ago"
      | none => "Chain not fully checked yet"))
  , caption (if m.backgroundRefreshAvailable then
      "iOS may also check while Winnow is closed, through the same routing. It cannot while the phone is off or after you force-quit Winnow."
    else "Background App Refresh is off, so Winnow checks the chain only while open.") ]

/-- Settings → Network → Sync. Its rows stay the same from pass to pass (a pass that starts or ends, an
error that comes and goes, changes them in place): the section sits above Transactions, and a row added or
removed every few seconds moved the list under the person's finger. -/
def syncSection (m : Model) : H :=
  let failed := m.phase == .peerDiscoveryFailed
  let warn (t : String) : H := warningRow t
  let status : H := match syncStatusText m.phase with
    | some t => if failed then warn t else .progress t
    | none => if m.status.syncing then .progress "Scanning filters…" else
      match m.status.lastSyncError with
      | some e => warn e
      | none => .labeled "Status" (if m.phase == .synced then "Up to date" else "Waiting to sync")
  .section "Sync" ""
    ([ .identified Ids.syncStatus status
     , .labeled "Filter scan" ((filterScanText m.phase m.status.nextScanHeight m.status.tipHeight).getD "—")
     , .labeled "Peers" s!"{m.status.peerCount}"
     , .identified Ids.syncLastError (.labeled "Last error" (m.status.lastSyncError.getD "None")) ] ++ chainCheckStatus m ++
     (match m.status.relayStoreQuarantined with | some q => [body q] | none => []) ++
     [if failed then .identified Ids.retryPeersButton (.button "Retry" .plain (some .retryPeers))
      else .button "Sync now" .plain (if m.status.syncing then none else some .syncNow)])

/-- Settings → Network → Sync: the confirmed balance and its coins, then the Sync section (records-test's
`syncBookkeeping`). -/
def syncSections (m : Model) : List H :=
  [ .section "" "" [.col ([caption "Balance · confirmed", balanceText m] ++
                    accountsBalanceLine m ++ [caption s!"{m.status.utxoCount} UTXO(s)"])]
  , syncSection m ]

/-! ### PaymentDetailView -/

def senderSection (m : Model) (h : HistoryItem) : H :=
  let locked := m.records.peopleStorageNotice.isSome
  let act (msg : HomeMsg) : Option Msg := if locked then none else some (.home msg)
  .section "Sender" ""
    (match receivedSender m.records h with
     | some p =>
       [.text p.name .title] ++
       (if p.payTo.isSome then [.button s!"Send to {p.name}" .plain (some (.home (.sendToPerson p.id)))]
        else [body "This label has no payment destination.",
              .button s!"Add destination for {p.name}" .plain (act (.attachSenderDestination p.id))]) ++
       [ .button "Change sender" .plain (act .labelSender)
       , .button "Remove sender label" .destructive (some (.home .removeSenderLabel)) ]
     | none => [.button "Save sender as person" .plain (act .labelSender)])

/-- The payment screen's "Account" section: the account a payment belongs to, with what can be done about it:
collecting a draft's signatures, or announcing again or giving up on a spend no block has taken. -/
def accountSection (m : Model) (p : DisplayedPayment) : List H :=
  match p.accountID.bind m.multisigInfo? with
  | none => []
  | some a =>
    let txid := p.item.txid
    let actions : List H :=
      if p.isDraft then
        [.identified Ids.collectSignaturesButton (.button "Collect signatures" .plain (some (.multisig (.openPSBT a.id))))]
      else if p.item.height == 0 && a.inFlight.contains txid then
        [ .identified Ids.rebroadcastSpendButton (.button "Rebroadcast" .plain (some (.multisig (.rebroadcast a.id txid))))
        , .identified Ids.abandonSpendButton (.button "Give up on this payment" .destructive (some (.multisig (.askAbandon a.id txid))))
        , caption "No block has taken this payment yet. Rebroadcast announces it to the network again; giving up frees its coins for another payment." ]
      else []
    [.section "Account" "" ([.identified Ids.paymentAccountName (.text a.name .title)] ++ actions)]

def paymentSections (m : Model) (txid : String) : List H :=
  match m.payment? txid with
  | none => [.section "" "" [body "This payment is no longer in the wallet’s history."]]
  | some row =>
    let h := row.item
    let locked := m.records.peopleStorageNotice.isSome
    let recipients := (paymentRecipients m.records h).map fun r =>
      let saved := (r.person.map (·.isSavedRecipient)).getD false
      .section "" ""
        ((match r.person with | some p => [.text p.name .title] | none => []) ++
         technical m s!"pay.addr.{r.id}" "Address" [copyableBlock m s!"pay.addr.{r.id}" r.address] ++
         [ body (satsText r.amount)
         , .button (if saved then "Rename recipient" else "Save recipient") .plain
             (if locked then none else some (.home (.editRecipient r.address (r.person.map (·.id))))) ] ++
         (match r.person with
          | some p => if saved then [.button "Remove from saved recipients" .destructive (some (.home (.removeRecipient p.id)))] else []
          | none => []))
    let labeled := labeledReceiveOutputs m.records h
    let labelSection : List H :=
      if labeled.isEmpty then [] else
      [.section "Receive address labels" "These are your local notes about the addresses paid. They do not verify who sent the payment."
        (labeled.flatMap fun o =>
          [.text o.label .title] ++ technical m s!"pay.label.{o.id}" "Address" [copyableBlock m s!"pay.label.{o.id}" o.address] ++
          [body (satsText o.amount), .button "Edit address label" .plain (some (.home (.editPaymentLabel o.address)))])]
    let notice : List H := match m.records.receiveLabelStorageNotice with
      | some n => [.section "" "" [body n]] | none => []
    let load : List H :=
      if h.outputs.isNone && h.spent > 0 && row.accountID.isNone then
        [.section "" "" [if m.payment.loading || m.status.syncing then .progress "Loading payment details…"
                         else .button "Load payment details" .plain (some (.home .loadPayment))]]
      else []
    -- the block, fee and replacement, then the txid and the explorer folded away, and Bump fee when the
    -- wallet can replace this payment
    let txSection : List H :=
      [.section "Details" ""
        ([ .identified Ids.paymentBlock (.labeled "Block" (if h.height > 0 then s!"{h.height}" else "Awaiting confirmation")) ] ++
         (match h.fee with | some f => [.identified Ids.paymentFee (.labeled "Fee" s!"{groupDigits f.natAbs} sats")] | none => []) ++
         (match h.replacedBy with
          | some r => [.identified Ids.paymentReplacedBy (.labeled "Replaced by" s!"{String.ofList (r.toList.take 8)}…")]
          | none => []) ++
         technical m "pay.txid" "Transaction ID"
           [ copyableIdentifier m "pay.txid" txid
           , explorerButton "View transaction" (m.settings.transactionURL txid) "transaction ID" ] ++
         (if m.status.feeBumpable.contains txid then [.identified Ids.bumpFeeButton (.button "Bump fee" .plain (some (.home .openFeeBump)))] else []))]
    [.section "" "" [paymentRow m row false]] ++ accountSection m row ++ recipients ++ labelSection ++ notice ++
    -- a payment out also receives its change: only money coming in has a sender
    (if h.net > 0 && !row.isDraft then [senderSection m h] else []) ++ load ++
    (match m.payment.error with | some e => [.section "" "" (errorRows (some e))] | none => []) ++ txSection

/-! ### FeeBumpView -/

/-- The fee bump sheet: the current rate, a higher one reviewed, Sign & replace (the `feeBumpReplaceConfirm`
journey, which has Core check the replacement). -/
def feeBumpSheet (m : Model) (inner : List H) : H :=
  let f := m.feeBump
  formSheet "Bump fee" (if f.bumping then none else some .closeSheet) [closeBar "Close"]
    ([ .section "Transaction" "" [ copyableIdentifier m "bump.txid" f.txid,
                                   .identified Ids.bumpCurrentRate (.labeled "Current rate" ((f.currentRateMilli.map feeRateText).getD "—")) ] ] ++
     (if f.replacement.isNone then
       [.section "Replacement fee" "The recipient and inputs stay the same. The extra fee comes from change; Winnow enforces a higher absolute fee, a higher feerate, and the incremental relay fee."
         [ .identified Ids.bumpRateField (.input .decimal "" "Higher rate (sat/vB)" f.targetText (fun s => .home (.setBumpRate s)) none)
         , .identified Ids.bumpReviewButton (.button "Review replacement" .plain
             (if (parseRateMilli f.targetText (trimNewlines := true)).isSome then some (.home .reviewBump) else none)) ]]
      else []) ++
     (match f.reviewed, f.replacement with
      | some (_, p), none =>
        [.section "Review" ""
          [ .labeled "Actual rate" (feeRateText p.feeRateMilli)
          , .identified Ids.bumpReplacementFee (.labeled "Replacement fee" (satsText p.fee))
          , .labeled "Change back" (match p.change with | some c => satsText c | none => "none (remainder becomes fee)")
          , .identified Ids.bumpSignButton (.button (if f.bumping then "Signing & broadcasting…" else "Sign & replace") .primary
              (if f.bumping then none else some (.home .bump))) ]]
      | _, _ => []) ++
     (match f.replacement with
      | some r => [.section "Replacement broadcast" ""
                    [ .row [.icon "arrow.triangle.2.circlepath", body "Original marked replaced"]
                    , copyableIdentifier m "bump.replacement" r
                    , .button "Done" .primary (some .closeSheet) ]]
      | none => []) ++
     (match f.error with | some e => [.section "" "" (errorRows (some e))] | none => [])) inner

end WinnowApp
