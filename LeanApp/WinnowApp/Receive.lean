import WinnowApp.Common

/-! ReceiveView.swift (label editor first, QR, copy/share/new address, explorer link, the mempool
window's unconfirmed rows), ReceiveAddressLabelEditor.swift and ShareMyCardView. -/

namespace WinnowApp
open LeanNative

def Model.receiveLabel? (m : Model) (address : String) : Option String := lookup m.records.receiveLabels address

/-- Leave the label editor: back to the address (Receive) or close the payment's label sheet. -/
def Model.finishLabel (m : Model) : Model × List Cmd :=
  if m.topSheet == some .labelEditor then m.closeTop
  else ({ m with receive := { m.receive with editingLabel := false }, labelEditor := { m.labelEditor with saving := false, error := none } }, [])

def stepReceive (msg : ReceiveMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  match msg with
  | .freshAddress =>
    if m.receive.changing then (m, []) else
    ({ m with receive := { m.receive with changing := true, error := none, unconfirmed := [] } },
     [.stopWatchingAddress, .receiveAddress g true])
  | .editLabel =>
    let a := m.receive.address
    ({ m with receive := { m.receive with editingLabel := true }, labelEditor := { address := a, draft := (m.receiveLabel? a).getD "" } }, [])
  | .setLabelDraft s => ({ m with labelEditor := { m.labelEditor with draft := s } }, [])
  | .saveLabel =>
    let e := m.labelEditor
    if e.saving then (m, []) else
    match normalizedLabel e.draft with
    | .ok l => if l.isEmpty then (m, []) else
      ({ m with labelEditor := { e with saving := true, error := none } }, [.setReceiveLabel g e.address e.draft])
    | .error _ => (m, [])
  | .removeLabel =>
    let e := m.labelEditor
    if e.saving then (m, []) else ({ m with labelEditor := { e with saving := true, error := none } }, [.setReceiveLabel g e.address ""])
  | .finishLabel => if m.labelEditor.saving then (m, []) else m.finishLabel
  | .openCard =>
    let name := m.settings.ownDisplayName.trimAscii.copy
    -- `journalCardShared()` as the card sheet appears
    ({ m with shareCard := {} }.present .shareCard,
     [.journal "card.shared" []] ++ (if name.isEmpty then [] else [.ownCard g name]))
  | .setOwnName s =>
    let st := { m.settings with ownDisplayName := s }
    let name := s.trimAscii.copy
    ({ m with settings := st, shareCard := { m.shareCard with card := if name.isEmpty then none else m.shareCard.card } },
     [.saveSettings st] ++ (if name.isEmpty then [] else [.ownCard g name]))

/-- The receive address arrived (first one, or a fresh one): the label editor comes first when the
address has no label yet, or always after New address; the mempool window opens on it. -/
def Model.onReceiveAddress (m : Model) (address : String) : Model × List Cmd :=
  let fresh := m.receive.changing
  let label := m.receiveLabel? address
  ({ m with receive := { m.receive with address, error := none, changing := false,
                                        editingLabel := fresh || label.isNone, unconfirmed := [] }
            labelEditor := { address, draft := label.getD "" } },
   [.watchAddress m.generation address])

/-! ## View -/

/-- `ReceiveAddressLabelEditor`. -/
def labelEditorView (m : Model) : List H :=
  let e := m.labelEditor
  let existing := m.receiveLabel? e.address
  let valid := normalizedLabel e.draft
  let notice := m.records.receiveLabelStorageNotice
  let canSave := match valid with
    | .ok l => !e.saving && !l.isEmpty && notice.isNone
    | .error _ => false
  [ .section "" "Name the person you’re sharing it with, or what the payment is for. This note will appear beside payments to this address."
      [.text "Who is this address for?" .headline]
  , .section "" "Only saved on this device. The label is not included when you copy or share the address, and does not verify who paid you."
      ([ .identified "receiveAddressLabelField"
          (.input .plain "" "Alice · invoice 12" e.draft (fun s => .receive (.setLabelDraft s)) (some (.receive .saveLabel))) ] ++
       (match valid with | .error msg => [body msg] | .ok _ => []) ++
       (match notice with | some n => [body n] | none => []) ++
       errorRows e.error)
  , .section "" ""
      ([ .identified "saveReceiveAddressLabelButton"
          (.button (if existing.isNone then "Save and show address" else "Save label") .primary (if canSave then some (.receive .saveLabel) else none))
       , .identified "skipReceiveAddressLabelButton"
          (.button (if existing.isNone then "Skip for now" else "Cancel") .plain (if e.saving then none else some (.receive .finishLabel))) ] ++
       (if existing.isSome then
         [.button "Remove label" .destructive (if e.saving || notice.isSome then none else some (.receive .removeLabel))] else [])) ]

def receiveSheet (m : Model) (inner : List H) : H :=
  let r := m.receive
  let a := r.address
  let content : List H :=
    if !a.isEmpty && r.editingLabel then labelEditorView m
    else if !a.isEmpty then
      let label := m.receiveLabel? a
      [ .section "" ""
          ((match label with | some l => [Html.symbol "tag" (.text l .headline)] | none => []) ++
           [ Html.symbol "tag" (.button (if label.isNone then "Label this address" else "Edit label") .plain (some (.receive .editLabel))) ])
      , .section "" "While this screen is open, incoming payments appear as unconfirmed within seconds. Everything else appears once it confirms in a block."
          ([ .col [.qr a, .identified "receiveAddress" (Html.centered (Html.mono (.text a .callout)))]
           , .row [.button (if m.copied == some "receive.address" then "Copied" else "Copy") .plain (some (.copy "receive.address" a)),
                   .share "Share" a,
                   .identified "freshAddressButton" (.button "New address" .plain (if r.changing then none else some (.receive .freshAddress)))]
           , explorerButton "View address" (m.settings.addressURL a) "address" ] ++
           (r.unconfirmed.map fun (_, amount) =>
             Html.symbol "clock" (Html.tone .warning (body s!"Unconfirmed: +{satsText amount} — awaiting confirmation")))) ]
    else if r.error.isNone then [.progress ""]
    else []
  formSheet "Receive" (some .closeSheet)
    [ closeBar "Done" "closeReceiveButton"
    , .toolbar [.button "Share my card" .plain (some (.receive .openCard))] ]
    (content ++ errorRows r.error) inner

/-- PaymentDetailView's "Address label" sheet. -/
def labelSheet (m : Model) (inner : List H) : H :=
  formSheet "Address label" (if m.labelEditor.saving then none else some .closeSheet) [] (labelEditorView m) inner

/-- `ShareMyCardView`: public keys only, plus the name others will see. -/
def shareCardSheet (m : Model) (inner : List H) : H :=
  formSheet "Share my card" (some .closeSheet) [closeBar "Done"]
    ([ .section "" "" [.input .plain "" "Your name, as others will see it" m.settings.ownDisplayName (fun s => .receive (.setOwnName s)) none] ] ++
     (match m.shareCard.card with
      | some card =>
        [.section "Your card" "This card carries public keys only. Anyone who has it can pay you and can see every address it derives, the same way your wallet does. People who pay you from their address book use the same list of addresses as your Receive screen, so two people paying at once can land on one address — a privacy detail, never a loss."
          [ .qr card, copyableBlock m "card.text" card ]]
      | none => [.section "" "" [caption "Add a name to make your card."]]) ++
     errorRows m.shareCard.error) inner

end WinnowApp
