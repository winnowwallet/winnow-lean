import WinnowApp.Multisig
import WinnowApp.Backup
import WinnowApp.Payments

/-! HomeView.swift and BeginnerHomeView.swift: the balance, sync and activity; HistoryRow,
PaymentDetailView (recipients, receive labels, sender, details, transaction) and FeeBumpView. -/

namespace WinnowApp
open ElmLean

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
  if m.settings.advancedMode then ({ m.switchTab 1 with routes := [] }, [.resolveRate m.generation inputs m.status.feeFloorMilli])
  else
    let m := if m.hasSheet .send then m else m.present .send
    (m, [.resolveRate m.generation inputs m.status.feeFloorMilli])

def stepHome (msg : HomeMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  match msg with
  | .openPayment txid => { m with routes := m.routes ++ [Route.payment txid], payment := {}, expanded := [] }.loadPayment
  | .openBackup => ({ m with routes := m.routes ++ [Route.backup] }, [])
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

/-- `HistoryRow`: who, the labels, the net amount, and Confirmed/Pending/Replaced (beginner) or the
block, fee and replacement (Advanced). The title opens the payment. The row, and its status lines. -/
def historyRow (m : Model) (h : HistoryItem) (tappable := true) : H × List H :=
  let labels := historyLabels m.records h
  let title := historyTitle m.records h
  let status : List H :=
    if m.settings.advancedMode then
      [ caption (match h.replacedBy with
          | some r => s!"replaced by {String.ofList (r.toList.take 8)}…"
          | none => if h.height > 0 then s!"block {h.height}" else "awaiting confirmation") ] ++
      (match h.fee with | some f => [caption s!"fee {groupDigits f.natAbs} sats"] | none => [])
    else
      [caption (if h.replacedBy.isSome then "Replaced" else if h.height > 0 then "Confirmed" else "Pending")]
  (.row [ .col ([.identified s!"historyPayment-{h.txid}"
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

/-- `HistoryRow` and `PaymentLink`: who (and which account), the labels, the amount, and Confirmed/Pending/
Replaced (Simple) or the block, fee and replacement (Advanced); a draft says how many signatures it has.
In Advanced mode a draft opens its collection step and anything else the payment; Simple mode opens only
the wallet's own payments (an account's rows are there to read, with no action). -/
def paymentRow (m : Model) (p : DisplayedPayment) (tappable := true) : H :=
  let h := p.item
  let labels := historyLabels m.records h
  let title := paymentTitle m p
  let advanced := m.settings.advancedMode
  let action : Option Msg :=
    if !tappable then none
    else match p.source, p.accountID with
      | .draft .., some id => if advanced then some (.multisig (.openPSBT id)) else none
      | .wallet, _ => some (.home (.openPayment h.txid))
      | _, _ => if advanced then some (.home (.openPayment h.txid)) else none
  let rowID := if p.isDraft then s!"historyDraft-{p.accountID.getD ""}" else s!"historyPayment-{h.txid}"
  let status : List H :=
    match p.source with
    | .draft _ signatures =>
      [.identified s!"transactionDraft-{h.txid}"
        (caption (if advanced then s!"{signatures} signed · tap to continue" else "Awaiting signatures · collected in Advanced mode"))]
    | _ => (historyRow m h).2
  let amount : H := match p.source with
    | .transfer _ _ moved => body s!"{groupDigits moved} sats"
    | _ => amountText h.net
  .row [ .col ([.identified rowID (match action with | some a => navLink title (some a) | none => body title)] ++
               (match p.source with
                | .account name => [.identified s!"paymentAccount-{h.txid}" (caption name)]
                | _ => []) ++
               (if labels.isEmpty then [] else [caption labels]))
       , .spacer
       , .col ([amount] ++ status) ]

def syncLine (m : Model) : H :=
  match m.phase.summary m.status.syncing with
  | .synced => .row [Html.tone .positive (.icon "checkmark.circle"), .identified "syncSummaryText" (caption "Up to date")]
  | .peersUnavailable => .identified "syncSummaryText" (body "Couldn't reach the Bitcoin network — check your connection.")
  | .syncing => .identified "syncSummaryText" (.progress "Syncing…")

/-- `AccountsBalanceLine`: how much of the headline sits in multisig accounts, which need co-signers to move;
nothing when the phone has no account. -/
def accountsBalanceLine (m : Model) : List H :=
  let count := m.multisig.accounts.length
  if count == 0 then [] else
  [.identified "accountsBalanceText"
    (caption s!"of which {satsText m.status.accountsBalance} in {count} multisig account{if count == 1 then "" else "s"}, needs co-signers")]

/-- The headline: the wallet's and the accounts' coins together. -/
def totalBalance (m : Model) : Int := m.status.balance + m.status.accountsBalance

/-- `PeerRoutingBanner`: Simple mode's routing line (a lock when every peer is behind Tor or I2P, a warning
when any peer can see the phone's IP address). -/
def peerRoutingBanner (m : Model) : H :=
  let state := PeerRoutingState.current m.settings.peerGatewaySettings.mode m.status.activeGateways m.status.discoveringGateways
  .identified "peerRoutingBanner" (.row [.icon state.symbol, caption state.message])

/-- The headline balance: the largest type in the app. -/
def balanceText (m : Model) : H := .identified "balanceText" (.text (satsText (totalBalance m)) .largeTitle)

/-- The balance card: one cell, the amount large, then its status line and the network's badge. -/
def balanceSection (m : Model) : H :=
  .section "" "" [.col ([ caption "Balance", balanceText m ] ++
                  accountsBalanceLine m ++ [
                    .row ([syncLine m] ++ (if m.settings.network == .mainnet then [] else
                      [.spacer, .identified "networkTag" (Html.badge (Html.tone .warning (caption "Signet · test coins")))])) ] ++
                  (if m.settings.network == .mainnet then [peerRoutingBanner m] else []) ++
                  (if m.phase.summary m.status.syncing == .peersUnavailable then
                    [.identified "retryPeersButton" (.button "Retry" .plain (some .retryPeers))] else []) ++
                  -- Simple mode waits out a dropped peer or two; Advanced shows every error
                  errorRows (simpleSyncError m.status.lastSyncError m.status.transientSyncError m.status.transientSyncFailures))]

def activitySection (m : Model) : H :=
  .section "Activity" ""
    (if m.status.payments.isEmpty then [caption "Nothing yet. Payments appear here once they are confirmed."]
     else m.status.payments.map (paymentRow m))

def beginnerSections (m : Model) : List H :=
  [ balanceSection m
  , .section "" "" [.row [.identified "receiveButton" (.button "Receive" .plain (some .openReceive)),
                          .identified "openSendButton" (.button "Send" .primary (some .openSend))]]
  , activitySection m
  , beginnerBackupSection m ]

/-- `ChainCheckStatus`: when a scan last reached the tip, and whether iOS may check in the background
(background checks are requests; iOS decides when they run). -/
def chainCheckStatus (m : Model) : List H :=
  [ .identified "lastCompleteChainCheck" (caption (match m.status.lastCheckedAgo with
      | some ago => s!"Chain last checked {ago} ago"
      | none => "Chain not fully checked yet"))
  , caption (if m.backgroundRefreshAvailable then
      "iOS may also check while Winnow is closed, through the same routing. It cannot while the phone is off or after you force-quit Winnow."
    else "Background App Refresh is off, so Winnow checks the chain only while open.") ]

/-- Advanced mode's Sync section. -/
def syncSection (m : Model) : H :=
  let statusText := syncStatusText m.phase
  .section "Sync" ""
    ((match statusText with
      | some t => if m.phase == .peerDiscoveryFailed then [body t, .button "Retry" .plain (some .retryPeers)]
                  else [.progress t]
      | none => []) ++
     (match filterScanText m.phase m.status.nextScanHeight m.status.tipHeight with
      | some t => [.labeled "Filter scan" t] | none => []) ++
     [.labeled "Peers" s!"{m.status.peerCount}"] ++ chainCheckStatus m ++
     (if m.status.syncing && statusText.isNone then [.progress "Scanning filters…"] else []) ++
     errorRows m.status.lastSyncError ++
     (match m.status.relayStoreQuarantined with | some q => [body q] | none => []) ++
     [.button "Sync now" .plain (if m.status.syncing then none else some .syncNow)])

def walletSections (m : Model) : List H :=
  [ .section "" "" [.col ([caption "Balance · confirmed", balanceText m] ++
                    accountsBalanceLine m ++ [caption s!"{m.status.utxoCount} UTXO(s)"])]
  , syncSection m
  , multisigSection m
  , .section "Transactions" ""
      (if m.status.payments.isEmpty then [caption "No transactions yet. Payments appear here once they confirm in a block."]
       else m.status.payments.map (paymentRow m)) ]

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

/-- The payment screen's "Account" section: the account a payment belongs to, with what can be done about it
in Advanced mode: collecting a draft's signatures, or announcing again or giving up on a spend no block has
taken. Simple mode names the account only. -/
def accountSection (m : Model) (p : DisplayedPayment) : List H :=
  match p.accountID.bind m.multisigInfo? with
  | none => []
  | some a =>
    let txid := p.item.txid
    let actions : List H :=
      if p.isDraft then
        if m.settings.advancedMode then
          [.identified "collectSignaturesButton" (.button "Collect signatures" .plain (some (.multisig (.openPSBT a.id))))]
        else [caption "This payment is waiting for the other signers. Signatures are collected in Advanced mode."]
      else if m.settings.advancedMode && p.item.height == 0 && a.inFlight.contains txid then
        [ .identified "rebroadcastSpendButton" (.button "Rebroadcast" .plain (some (.multisig (.rebroadcast a.id txid))))
        , .identified "abandonSpendButton" (.button "Give up on this payment" .destructive (some (.multisig (.askAbandon a.id txid))))
        , caption "No block has taken this payment yet. Rebroadcast announces it to the network again; giving up frees its coins for another payment." ]
      else []
    [.section "Account" "" ([.identified "paymentAccountName" (.text a.name .title)] ++ actions)]

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
    let txSection : List H :=
      if m.settings.advancedMode then
        [.section "Transaction" ""
          ([ copyableIdentifier m "pay.txid" txid
           , explorerButton "View transaction" (m.settings.transactionURL txid) "transaction ID" ] ++
           (if m.status.feeBumpable.contains txid then [.button "Bump fee" .plain (some (.home .openFeeBump))] else []))]
      else [.section "" "" (technical m "pay.txid" "Transaction ID" [copyableIdentifier m "pay.txid" txid])]
    [.section "" "" [paymentRow m row false]] ++ accountSection m row ++ recipients ++ labelSection ++ notice ++
    (if h.received > 0 && !row.isDraft then [senderSection m h] else []) ++ load ++
    (match m.payment.error with | some e => [.section "" "" (errorRows (some e))] | none => []) ++ txSection

/-! ### FeeBumpView -/

def feeBumpSheet (m : Model) (inner : List H) : H :=
  let f := m.feeBump
  formSheet "Bump fee" (if f.bumping then none else some .closeSheet) [closeBar "Close"]
    ([ .section "Transaction" "" [ copyableIdentifier m "bump.txid" f.txid,
                                   .labeled "Current rate" ((f.currentRateMilli.map feeRateText).getD "—") ] ] ++
     (if f.replacement.isNone then
       [.section "Replacement fee" "The recipient and inputs stay the same. The extra fee comes from change; Winnow enforces a higher absolute fee, a higher feerate, and the incremental relay fee."
         [ .input .decimal "" "Higher rate (sat/vB)" f.targetText (fun s => .home (.setBumpRate s)) none
         , .button "Review replacement" .plain (if (parseRateMilli f.targetText (trimNewlines := true)).isSome then some (.home .reviewBump) else none) ]]
      else []) ++
     (match f.reviewed, f.replacement with
      | some (_, p), none =>
        [.section "Review" ""
          [ .labeled "Actual rate" (feeRateText p.feeRateMilli)
          , .labeled "Replacement fee" (satsText p.fee)
          , .labeled "Change back" (match p.change with | some c => satsText c | none => "none (remainder becomes fee)")
          , .button (if f.bumping then "Signing & broadcasting…" else "Sign & replace") .primary
              (if f.bumping then none else some (.home .bump)) ]]
      | _, _ => []) ++
     (match f.replacement with
      | some r => [.section "Replacement broadcast" ""
                    [ .row [.icon "arrow.triangle.2.circlepath", body "Original marked replaced"]
                    , copyableIdentifier m "bump.replacement" r
                    , .button "Done" .primary (some .closeSheet) ]]
      | none => []) ++
     (match f.error with | some e => [.section "" "" (errorRows (some e))] | none => [])) inner

end WinnowApp
