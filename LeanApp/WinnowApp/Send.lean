import WinnowApp.Multisig
import WinnowApp.Ids

/-! SendView.swift as the one Send sheet: the form (From when an account exists, address or saved person,
amount, the fee folded away and Normal by default), the review with Winnow's four warnings and its folded
transaction details, and the status with the relay log. -/

namespace WinnowApp
open LeanNative

/-- `SendView.reviewInputs`: what a preview must have been made for; a person's payment index is part of it,
so a review for an earlier address is void. -/
def Model.sendInputs (m : Model) : SendInputs :=
  let i := m.send.inputs
  let person := i.personID.bind m.person? |>.filter (·.isSavedRecipient)
  let account := i.accountID.bind m.multisigInfo?
  { i with destination := if person.isSome then "" else i.destination
           network := m.settings.network
           personID := person.map (·.id)
           paymentIndex := person.map (·.nextPaymentIndex)
           walletID := m.walletID
           -- an account no longer on this phone is the wallet's
           accountID := account.map (·.id)
           -- the recovery path only for an account that has one
           recovery := i.recovery && account.any (·.hasRecovery) }

/-- An edit of the form voids the preview, unless a payment is being sent or was sent. -/
def Model.editSend (m : Model) (f : SendInputs → SendInputs) (rerate := false) : Model × List Cmd :=
  if m.send.sending || m.send.sentTxid.isSome then (m, [])
  else
    let m' := { m with send := { m.send with inputs := f m.send.inputs, preview := none, error := none } }
    (m', if rerate then [.resolveRate m.generation m'.sendInputs m.status.feeFloorMilli] else [])

def stepSend (msg : SendMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  match msg with
  | .setDestination t => m.editSend fun i => { i with destination := t }
  | .setAmount t => m.editSend fun i => { i with amount := t }
  | .setPriority p => m.editSend (fun i => { i with priority := p }) true
  | .setOverride t => m.editSend (fun i => { i with override := t }) true
  | .pasteDestination => (m, [.paste .destination])
  | .openRecipients => (m.present .savedRecipients, [])
  | .choosePerson id => m.editSend fun i => { i with personID := some id, destination := "" }
  | .clearPerson => m.editSend fun i => { i with personID := none }
  | .setSource a => m.editSend fun i => { i with accountID := a, recovery := false }
  | .setRecovery b => m.editSend fun i => { i with recovery := b }
  | .review =>
    let inputs := m.sendInputs
    if m.send.reviewing || m.send.sending || !canReview inputs then (m, []) else
    match inputs.amount.trimAscii.copy.toNat? with
    | some a =>
      if a == 0 then ({ m with send := { m.send with error := some "Enter an amount in sats." } }, []) else
      ({ m with send := { m.send with reviewing := true, error := none, preview := none } }, [.previewSend g inputs])
    | none => ({ m with send := { m.send with error := some "Enter an amount in sats." } }, [])
  | .sendPayment =>
    match m.send.preview with
    | none => (m, [])
    | some p =>
      if m.send.sending then (m, []) else
      if m.spendingInFlight then
        (m.fail "send" "Another payment is already being signed and broadcast. Wait for it to finish.", [])
      else
        -- an account's payment is signed here and goes out from the collection step
        let cmd := if p.account.isSome then Cmd.signAndDraft g m.sendInputs p
          else .sendPayment g m.sendInputs p
        ({ m with send := { m.send with sending := true, error := none }, spendingInFlight := true }, [cmd])
  | .editPayment => if m.send.sending then (m, []) else ({ m with send := { m.send with preview := none, error := none } }, [])
  | .newPayment =>
    ({ m with send := { inputs := { network := m.settings.network } },
              expanded := (m.expanded.erase "send.details").erase "send.fee" |>.erase "send.review" },
     [.resolveRate g { network := m.settings.network } m.status.feeFloorMilli])

/-- A relay event about the sent transaction (SendView's `apply`). -/
def Model.onRelay (m : Model) (txid : String) (e : RelayEvent) : Model :=
  if m.send.sentTxid != some txid then m else
  let s := m.send
  let s := match e with
    | .announced n => { s with relayLog := s.relayLog ++ [s!"Announced to {n} peer(s)"] }
    | .requested peer =>
      if s.relayedPeers.contains peer then s
      else { s with relayedPeers := s.relayedPeers ++ [peer], relayLog := s.relayLog ++ [s!"Relayed to {peer}"] }
    | .echoed peer => if s.relayedPeers.contains peer then s else { s with relayedPeers := s.relayedPeers ++ [peer] }
    | .feeFloorExceeded => { s with feeFloorNotice := true }
    | .confirmed =>
      match m.historyItem? txid with
      | some h => if h.height > 0 then { s with confirmedHeight := some h.height } else s
      | none => s
  { m with send := s }

/-! ## View -/

/-- The fee priorities (1, Normal, is the default). -/
def feePriorityLabels : List String := ["Low", "Normal", "High"]

def feePriorityLabel (i : Nat) : String := (feePriorityLabels[i]?).getD "Normal"

/-- From (when this phone has accounts): the wallet, or a multisig account whose payment needs the other
signers before it goes out. -/
def sourceSection (m : Model) : List H :=
  if m.multisig.accounts.isEmpty then [] else
  let selected := m.sendInputs.accountID
  let row (title : String) (balance : Int) (id : Option String) (identifier : String) : H :=
    .identified identifier
      (.row ([.button s!"{title} · {satsText balance}" .plain (some (.send (.setSource id))), .spacer] ++
             (if selected == id then [.icon "checkmark"] else [])))
  [.section "From" ""
    ([row "Wallet" m.status.balance none Ids.sendFromWallet] ++
     (m.multisig.accounts.map fun a =>
        row (a.name ++ (if a.draft.isNone then "" else " · awaiting signatures")) a.balance (some a.id) (Ids.sendFrom (a.id))) ++
     (match selected.bind m.multisigInfo? with
      | some a =>
        let recovery := m.sendInputs.recovery
        -- the recovery path, here and not on the account page (PORT.md: one Send)
        (match a.recovery with
         | some r =>
           [ .identified Ids.multisigPathPicker
               (.picker "Spend with" ["Signers now", "Recovery path"] (if recovery then 1 else 0) (fun i => .send (.setRecovery (i == 1))))
           ] ++ (if recovery then
             [.identified Ids.sendRecoveryNote (caption s!"Only coins that have not moved for the recovery delay can be spent this way ({r}).")]
            else [])
         | none => []) ++
        [.identified Ids.sendSourceNote
          (caption (if recovery then "You sign here; the payment goes out once the recovery path's signatures are in."
                    else s!"Needs {a.policy.getD "?"}. You sign here; the payment goes out once the other signatures are in."))]
      | none => []))]

def sendForm (m : Model) : List H :=
  let i := m.send.inputs
  let inputs := m.sendInputs
  let person := inputs.personID.bind m.person?
  let send (f : String → SendMsg) : String → Msg := fun s => .send (f s)
  let toSection : H :=
    .section "To" ""
      (match person with
       | some p => [.row [body p.name, .spacer, .button "Change" .plain (some (.send .clearPerson))]]
       | none =>
         [ .row [.identified Ids.destinationField (.input .plain "" "Bitcoin address" i.destination (send .setDestination) none),
                 .identified Ids.pasteDestinationButton (.button "Paste" .plain (some (.send .pasteDestination)))]
         , .button "Saved recipients" .plain (some (.send .openRecipients)) ])
  sourceSection m ++ [toSection,
    .section "Amount" "You'll see the network fee before you send."
      [ .row [.identified Ids.amountField (.input .number "" "0" i.amount (send .setAmount) none), caption "sats"] ] ] ++
  -- folded, and Normal until changed
  [ .section "" (if m.isExpanded "send.fee" then "The rate uses your override, recent confirmed fees, or a preset, never below the peers' relay floor. It is not a live fee-market estimate." else "")
      [ .identified Ids.sendFeeDisclosure (.disclosure s!"Fee · {feePriorityLabel i.priority}{if i.override.trimAscii.isEmpty then "" else " · override"}"
          (m.isExpanded "send.fee") (Msg.setExpanded "send.fee")
          [ .picker "Priority" feePriorityLabels i.priority (fun n => .send (.setPriority n))
          , .identified Ids.resolvedRateText (.labeled "Resolved rate" ((m.send.resolvedRateMilli.map feeRateText).getD "Set at review"))
          , .identified Ids.feeFloorText (.labeled "Network floor" ((m.status.feeFloorMilli.map feeRateText).getD "unknown"))
          -- a decimal rate: the number pad has no decimal point
          , .identified Ids.feeOverrideField (.input .decimal "" "Override (sat/vB, optional)" i.override (send .setOverride) none) ]) ] ] ++
  [ .section "" ""
      [ .identified Ids.reviewButton (.button (if m.send.reviewing then "Preparing review…" else "Review payment") .primary
          (if m.send.reviewing || !canReview inputs then none else some (.send .review))) ] ]

def paymentAmounts (p : Preview) : H :=
  .section "" "" [ .identified Ids.reviewAmount (.labeled "Amount" (satsText p.amount)),
                   .identified Ids.reviewFee (.labeled "Network fee" (satsText p.fee)),
                   .identified Ids.reviewTotal (.labeled "Total" (satsText (p.amount + p.fee))) ]

/-- A warning on the review; backend-test's `peopleFlow` reaches all four of `sendReview`'s. -/
def warning (iconName text : String) : H := .section "" "" [warningRow text iconName]

def sendReview (m : Model) (p : Preview) : List H :=
  let warnings : List H :=
    (match p.recipient with
     | some r =>
       (if r.hasUnverifiedFundingDestination then
         [warning "exclamationmark.triangle" s!"This destination was inferred from transaction funding. Winnow has not verified that it belongs to {r.name}. Confirm it with them before sending."] else []) ++
       (if !r.derivesFreshAddresses then
         [warning "eye" s!"This address has been saved for reuse. Repeated payments can be linked. Ask {r.name} for a fresh address or Winnow contact card."] else [])
     | none => []) ++
    (match feeProportionWarning p.amount p.fee with | some w => [warning "exclamationmark.triangle" w] | none => []) ++
    (if p.locktimeLagsTip then
      [warning "clock.arrow.circlepath" "Your wallet is still syncing. Sending now can reveal that on the Bitcoin network. Wait for sync to finish for better privacy."]
     else [])
  let action := if m.send.sending then "Working…" else if p.account.isSome then "Sign and continue" else "Send payment"
  [ .section "To" "" ((match p.recipient with | some r => [body r.name] | none => []) ++
                      [.identified Ids.reviewDestination (literal p.destination)] ++
                      -- the one visible difference of a BIP352 send: the chain shows an address never typed
                      (if p.silent then
                        [.identified Ids.silentPaymentNote
                          (caption "Silent payment: the Bitcoin address this pays is created for this transaction only.")]
                       else []))
  , paymentAmounts p ] ++
  (match p.account with
   | some a =>
     [.section "" "Sign and continue adds this phone's signature and keeps the payment under Transactions until the other signers have signed."
       ([ .labeled "From" a.name ] ++
        (if a.recovery then [.identified Ids.reviewSpendPath (.labeled "Spend with" "Recovery path")]
         else [.identified Ids.reviewSignatures (.labeled "Signatures" s!"needs {a.threshold} of {a.signerCount}")]))]
   | none => []) ++ warnings ++
  [ .section "" ""
      [ .identified Ids.sendButton (.button action .primary (if m.send.sending then none else some (.send .sendPayment)))
      , .button "Edit payment" .plain (if m.send.sending then none else some (.send .editPayment)) ] ] ++
  [ .section "" ""
      [ .identified Ids.reviewDetailsDisclosure (.disclosure "Transaction details" (m.isExpanded "send.review") (Msg.setExpanded "send.review")
          ([ .labeled "Rate" (feeRateText p.feeRateMilli), .labeled "Inputs" s!"{p.inputCount}" ] ++
           (match p.change with | some c => [.labeled "Change back" (satsText c)] | none => []) ++
           -- what the source holds now, as the wallet last read it (a review made before a block can go stale)
           [.identified Ids.reviewBalance (.labeled "Balance now" (satsText (match p.account with
              | some a => ((m.multisigInfo? a.id).map (·.balance)).getD 0
              | none => m.status.balance)))])) ] ]

def sendStatus (m : Model) (txid : String) : List H :=
  let s := m.send
  [ .section ""  ""
      ((if s.confirmedHeight.isSome then [.row [Html.tone .positive (.icon "checkmark.circle.fill"), .identified Ids.broadcastConfirmed (body "Payment confirmed")]]
        else if ((m.historyItem? txid).bind (·.replacedBy)).isSome then
          [.row [Html.tone .warning (.icon "exclamationmark.triangle.fill"), .identified Ids.broadcastReplaced (body "Replaced")],
           caption "This transaction will not confirm: another one spent its coins."]
        else [.row [Html.tone .warning (.icon "clock"), .identified Ids.broadcastPending (body "Waiting for confirmation")],
              caption "You can close this screen. The payment stays in Activity until it confirms."]) ++
       (if s.feeFloorNotice then
         [warningRow "The network now requires a higher fee. This payment may be delayed. Raise its fee with Bump fee on its screen in Activity."]
        else [])) ] ++
  (match s.preview with
   | some p => [paymentAmounts p] ++ (match p.account with
       | some a => [.section "" "" [.labeled "From" a.name]]
       | none => [])
   | none => []) ++
  -- Activity and explorers show the derived address, not the code: the receipt is where the two meet
  (if s.derivedAddresses.isEmpty then [] else
    [.section "Paid on chain to" "" (s.derivedAddresses.map fun a => .identified Ids.derivedOutputAddress (literal a))]) ++
  [ .section "" "" [ .identified Ids.newPaymentButton (.button "New payment" .primary (some (.send .newPayment))) ]
  , .section "" ""
      [ .disclosure "Transaction details" (m.isExpanded "send.details") (Msg.setExpanded "send.details")
          ([ copyableIdentifier m "send.txid" txid ] ++
           (match s.rawTransaction, s.confirmedHeight with
            | some raw, none => [copyableIdentifier m "send.raw" raw (abbreviated := true) (label := "Copy raw transaction")]
            | _, _ => []) ++
           [ explorerButton "View transaction" (m.settings.transactionURL txid) "transaction ID" ] ++
           (if s.relayedPeers.isEmpty then [] else [body s!"Relayed to {s.relayedPeers.length} peer(s)"]) ++
           s.relayLog.map caption ++
           (match s.confirmedHeight with | some h => [.labeled "Block" s!"{h}"] | none => [])) ] ]

def sendContent (m : Model) : List H :=
  (match m.send.sentTxid, m.send.collecting, m.send.preview with
   | some t, _, _ => sendStatus m t
   | none, some id, _ => collectSections m id
   | none, none, some p => sendReview m p
   | none, none, none => sendForm m) ++
  (match m.send.error with | some e => [.section "" "" (errorRows (some e))] | none => [])

def sendTitle (m : Model) : String :=
  if m.send.sentTxid.isSome then "Payment" else if m.send.collecting.isSome then "Collect signatures"
  else if m.send.preview.isSome then "Review payment" else "Send"

/-- The Send sheet (Send on the home, a saved person, an account's "Send from this account"). -/
def sendSheet (m : Model) (inner : List H) : H :=
  formSheet (sendTitle m) (if m.send.sending then none else some .closeSheet)
    [if m.send.sentTxid.isNone then closeBar "Cancel" Ids.closeSendButton
     else .toolbar [.identified Ids.closeSendButton (.button "Done" .primary (some .closeSheet))] .confirm]
    (sendContent m) inner

end WinnowApp
