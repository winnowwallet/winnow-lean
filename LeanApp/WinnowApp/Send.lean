import WinnowApp.Multisig

/-! SendView.swift: the form (address or saved person, amount, Advanced fee controls), the review with
Winnow's four warnings, and the status with the relay log. -/

namespace WinnowApp
open ElmLean

/-- `SendView.reviewInputs`: what a preview must have been made for. Priority and override count only
in Advanced mode; a person's payment index is part of it, so a review for an earlier address is void. -/
def Model.sendInputs (m : Model) : SendInputs :=
  let i := m.send.inputs
  let person := i.personID.bind m.person? |>.filter (·.isSavedRecipient)
  let account := if m.settings.advancedMode then i.accountID.bind m.multisigInfo? else none
  { i with destination := if person.isSome then "" else i.destination
           priority := if m.settings.advancedMode then i.priority else 1
           override := if m.settings.advancedMode then i.override else ""
           network := m.settings.network
           personID := person.map (·.id)
           paymentIndex := person.map (·.nextPaymentIndex)
           walletID := m.walletID
           -- From is Advanced mode's: a Simple-mode review is always the wallet's
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
        let cmd := if p.account.isSome then Cmd.signAndDraft g m.settings.advancedMode m.sendInputs p
          else .sendPayment g m.sendInputs p
        ({ m with send := { m.send with sending := true, error := none }, spendingInFlight := true }, [cmd])
  | .editPayment => if m.send.sending then (m, []) else ({ m with send := { m.send with preview := none, error := none } }, [])
  | .newPayment =>
    ({ m with send := { inputs := { network := m.settings.network } } }, [.resolveRate g { network := m.settings.network } m.status.feeFloorMilli])

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

/-- From (Advanced mode, when this phone has accounts): the wallet, or a multisig account whose payment needs
the other signers before it goes out. -/
def sourceSection (m : Model) : List H :=
  if !m.settings.advancedMode || m.multisig.accounts.isEmpty then [] else
  let selected := m.sendInputs.accountID
  let row (title : String) (balance : Int) (id : Option String) (identifier : String) : H :=
    .identified identifier
      (.row ([.button s!"{title} · {satsText balance}" .plain (some (.send (.setSource id))), .spacer] ++
             (if selected == id then [.icon "checkmark"] else [])))
  [.section "From" ""
    ([row "Wallet" m.status.balance none "sendFromWallet"] ++
     (m.multisig.accounts.map fun a =>
        row (a.name ++ (if a.draft.isNone then "" else " · awaiting signatures")) a.balance (some a.id) s!"sendFrom-{a.id}") ++
     (match selected.bind m.multisigInfo? with
      | some a =>
        let recovery := m.sendInputs.recovery
        -- the recovery path, here and not on the account page (PORT.md: one Send)
        (match a.recovery with
         | some r =>
           [ .identified "multisigPathPicker"
               (.picker "Spend with" ["Signers now", "Recovery path"] (if recovery then 1 else 0) (fun i => .send (.setRecovery (i == 1))))
           ] ++ (if recovery then
             [.identified "sendRecoveryNote" (caption s!"Only coins that have not moved for the recovery delay can be spent this way ({r}).")]
            else [])
         | none => []) ++
        [.identified "sendSourceNote"
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
         [ .row [.identified "destinationField" (.input .plain "" "Bitcoin address" i.destination (send .setDestination) none),
                 .identified "pasteDestinationButton" (.button "Paste" .plain (some (.send .pasteDestination)))]
         , .button "Saved recipients" .plain (some (.send .openRecipients)) ])
  sourceSection m ++ [toSection,
    .section "Amount" "You'll see the network fee before you send."
      [ .row [.identified "amountField" (.input .number "" "0" i.amount (send .setAmount) none), caption "sats"] ] ] ++
  (if m.settings.advancedMode then
    [ .section "Fee" "The rate uses your override, recent confirmed fees, or a preset, never below the peers' relay floor. It is not a live fee-market estimate."
        [ .picker "Priority" ["Low", "Medium", "High"] i.priority (fun n => .send (.setPriority n))
        , .labeled "Resolved rate" ((m.send.resolvedRateMilli.map feeRateText).getD "—")
        , .labeled "Network floor" ((m.status.feeFloorMilli.map feeRateText).getD "unknown")
        -- a decimal rate: the number pad has no decimal point
        , .input .decimal "" "Override (sat/vB, optional)" i.override (send .setOverride) none ] ]
   else []) ++
  [ .section "" ""
      [ .identified "reviewButton" (.button (if m.send.reviewing then "Preparing review…" else "Review payment") .primary
          (if m.send.reviewing || !canReview inputs then none else some (.send .review))) ] ]

def paymentAmounts (p : Preview) : H :=
  .section "" "" [ .identified "reviewAmount" (.labeled "Amount" (satsText p.amount)),
                   .identified "reviewFee" (.labeled "Network fee" (satsText p.fee)),
                   .identified "reviewTotal" (.labeled "Total" (satsText (p.amount + p.fee))) ]

def warning (iconName text : String) : H := .section "" "" [.row [Html.tone .warning (.icon iconName), caption text]]

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
                      [.identified "reviewDestination" (literal p.destination)] ++
                      -- the one visible difference of a BIP352 send: the chain shows an address never typed
                      (if p.silent then
                        [.identified "silentPaymentNote"
                          (caption "Silent payment: the Bitcoin address this pays is created for this transaction only.")]
                       else []))
  , paymentAmounts p ] ++
  (match p.account with
   | some a =>
     [.section "" "Sign and continue adds this phone's signature and keeps the payment under Transactions until the other signers have signed."
       ([ .labeled "From" a.name ] ++
        (if a.recovery then [.identified "reviewSpendPath" (.labeled "Spend with" "Recovery path")]
         else [.identified "reviewSignatures" (.labeled "Signatures" s!"needs {a.threshold} of {a.signerCount}")]))]
   | none => []) ++ warnings ++
  [ .section "" ""
      [ .identified "sendButton" (.button action .primary (if m.send.sending then none else some (.send .sendPayment)))
      , .button "Edit payment" .plain (if m.send.sending then none else some (.send .editPayment)) ] ] ++
  (if m.settings.advancedMode then
    [ .section "Transaction details" ""
        ([ .labeled "Rate" (feeRateText p.feeRateMilli), .labeled "Inputs" s!"{p.inputCount}" ] ++
         (match p.change with | some c => [.labeled "Change back" (satsText c)] | none => [])) ]
   else [])

def sendStatus (m : Model) (txid : String) : List H :=
  let s := m.send
  [ .section ""  ""
      ((if s.confirmedHeight.isSome then [.row [Html.tone .positive (.icon "checkmark.circle.fill"), .identified "broadcastConfirmed" (body "Payment confirmed")]]
        else [.row [Html.tone .warning (.icon "clock"), .identified "broadcastPending" (body "Waiting for confirmation")],
              caption (if m.settings.advancedMode then "You can leave this screen. Follow this payment in Wallet."
                       else "You can close this screen. The payment stays in Activity until it confirms.")]) ++
       (if s.feeFloorNotice then
         [.row [.icon "exclamationmark.triangle", caption "The network now requires a higher fee. This payment may be delayed. Advanced mode lets you raise its fee in Wallet."]]
        else [])) ] ++
  (match s.preview with
   | some p => [paymentAmounts p] ++ (match p.account with
       | some a => [.section "" "" [.labeled "From" a.name]]
       | none => [])
   | none => []) ++
  -- Activity and explorers show the derived address, not the code: the receipt is where the two meet
  (if s.derivedAddresses.isEmpty then [] else
    [.section "Paid on chain to" "" (s.derivedAddresses.map fun a => .identified "derivedOutputAddress" (literal a))]) ++
  [ .section "" "" [ .identified "newPaymentButton" (.button "New payment" .primary (some (.send .newPayment))) ]
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

/-- Beginner mode's Send sheet. -/
def sendSheet (m : Model) (inner : List H) : H :=
  formSheet (sendTitle m) (if m.send.sending then none else some .closeSheet)
    [if m.send.sentTxid.isNone then closeBar "Cancel" "closeSendButton"
     else .toolbar [.identified "closeSendButton" (.button "Done" .primary (some .closeSheet))] .confirm]
    (sendContent m) inner

end WinnowApp
