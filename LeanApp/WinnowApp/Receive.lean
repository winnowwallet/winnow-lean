import WinnowApp.Common
import WinnowApp.Ids

/-! Receive: one page. The wallet's address at once (QR, copy/share/new address, an optional label, the explorer
link, the mempool window's unconfirmed rows), and under it "From one person": a name gives that person's own
address and their card (issue #94). Upstream's ReceiveView.swift asked for a label before it showed an address,
and kept the card on a sheet of its own (ShareMyCardView); here neither is a step. -/

namespace WinnowApp
open LeanNative

def Model.receiveLabel? (m : Model) (address : String) : Option String := lookup m.records.receiveLabels address

/-- Leave the label editor: back to the address (Receive) or close the payment's label sheet. -/
def Model.finishLabel (m : Model) : Model × List Cmd :=
  if m.topSheet == some .labelEditor then m.closeTop
  else ({ m with receive := { m.receive with editingLabel := false }, labelEditor := { m.labelEditor with saving := false, error := none } }, [])

/-- Receive, its label editor and the share card (records-test's `receiveScreen`). -/
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
  | .setOwnName s =>
    let st := { m.settings with ownDisplayName := s }
    -- a card made under the old name is not the card to hand over under the new one
    ({ m with settings := st, shareCard := { m.shareCard with personCard := none, personAddress := none } }, [.saveSettings st])
  | .setCardFor s =>
    let kept := m.shareCard.personCard.filter (·.1 == s.trimAscii.copy)
    -- typed over, the name is what is meant, not the person the sheet was opened for
    let address := if kept.isSome then m.shareCard.personAddress else none
    ({ m with shareCard := { m.shareCard with forName := s, forPerson := none, personCard := kept, personAddress := address, error := none } }, [])
  | .makePersonCard =>
    -- the wallet's own name is what the card says it is from; without one the person names it themselves
    let own := m.settings.ownDisplayName.trimAscii.copy
    let person := m.shareCard.forName.trimAscii.copy
    if m.shareCard.making || person.isEmpty then (m, []) else
    ({ m with shareCard := { m.shareCard with making := true, error := none } }, [.personCard g m.shareCard.forPerson person own])

/-- The receive address arrived (first one, or a fresh one): it is shown at once, and the mempool window
opens on it. A label is asked for only when the person taps "Label this address". -/
def Model.onReceiveAddress (m : Model) (address : String) : Model × List Cmd :=
  let label := m.receiveLabel? address
  ({ m with receive := { m.receive with address, error := none, changing := false, editingLabel := false, unconfirmed := [] }
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
      ([ .identified Ids.receiveAddressLabelField
          (.input .plain "" "Alice · invoice 12" e.draft (fun s => .receive (.setLabelDraft s)) (some (.receive .saveLabel))) ] ++
       (match valid with | .error msg => [body msg] | .ok _ => []) ++
       (match notice with | some n => [body n] | none => []) ++
       errorRows e.error)
  , .section "" ""
      ([ .identified Ids.saveReceiveAddressLabelButton
          (.button "Save label" .primary (if canSave then some (.receive .saveLabel) else none))
       , .identified Ids.skipReceiveAddressLabelButton
          (.button "Cancel" .plain (if e.saving then none else some (.receive .finishLabel))) ] ++
       (if existing.isSome then
         [.button "Remove label" .destructive (if e.saving || notice.isSome then none else some (.receive .removeLabel))] else [])) ]

/-- "From one person" (issue #94): their name, and then what to give them. An ordinary address of their own,
which any wallet or an exchange can pay, and a card for the case that they use Winnow, which carries a code
made for them under a card's own prefix (`winnowcard1p…`: their shared secret and a spend key of their own,
and neither of the wallet's keys). Both are the same card underneath: the address is its next unpaid one. -/
def personCardSections (m : Model) : List H :=
  let sc := m.shareCard
  let person := sc.forName.trimAscii.copy
  let known : Bool := match sc.forPerson with
    | some id => m.records.people.any fun p => p.id == id && p.hasCard
    | none => ((m.records.people.find? (·.name == person)).map (·.hasCard)).getD false
  let shown := sc.personCard.filter (·.1 == person)
  let label := if sc.making then "Making…" else if person.isEmpty then "Make their address and card"
    else if known then s!"Show {person}’s address and card" else s!"Make {person}’s address and card"
  [ .section "From one person" "For one person and nobody else. What they pay is named as theirs, at addresses only the two of you can work out, and they cannot see your other addresses. Give these only to them: anyone who has them can see what is paid with them."
      ([ .identified Ids.personCardNameField
          (.input .plain "" "Their name" sc.forName (fun s => .receive (.setCardFor s)) (some (.receive .makePersonCard))) ] ++
       -- once shown, the button has done its work
       (if shown.isSome then [] else
         [ .identified Ids.makePersonCardButton
             (.button label .plain (if sc.making || person.isEmpty then none else some (.receive .makePersonCard))) ]) ++
       -- these are rows of this section: as sections of their own they were drawn with the next section's
       -- footer under them (seen in the simulator, 2026-11-14)
       (match shown with
        | some (name, card) =>
          -- first what any payer can use: the next unpaid address of this person's card
          (match sc.personAddress with
           | some address =>
             [ .text s!"An address for {name}" .headline
             , caption "For any wallet or an exchange. It changes once it has been paid."
             , .qr address, copyableBlock m "card.address" address Ids.personAddressText ]
           | none => []) ++
          [ .text s!"A card for {name}" .headline
          , caption s!"If {name} uses Winnow, give them this instead: every payment then gets an address of its own, with nothing more to ask you for."
          , .qr card, copyableBlock m "card.person" card Ids.personCardText
          , .identified Ids.ownNameField
              (.input .plain "" "Your name on the card (optional)" m.settings.ownDisplayName (fun s => .receive (.setOwnName s)) none) ]
        | none => [])) ]

def receiveSheet (m : Model) (inner : List H) : H :=
  let r := m.receive
  let a := r.address
  let content : List H :=
    if !a.isEmpty && r.editingLabel then labelEditorView m
    else if !a.isEmpty then
      let label := m.receiveLabel? a
      [ .section "" "While this screen is open, incoming payments appear as unconfirmed within seconds. Everything else appears once it confirms in a block."
          ((match label with | some l => [Html.symbol "tag" (.text l .headline)] | none => []) ++
           [ .col [.qr a, .identified Ids.receiveAddress (Html.centered (Html.mono (.text a .callout)))]
           -- two to a row: with New address beside them the words broke across lines (seen in the simulator)
           , .row [.button (if m.copied == some "receive.address" then "Copied" else "Copy") .plain (some (.copy "receive.address" a)),
                   .share "Share" a]
           , .identified Ids.freshAddressButton
               (Html.symbol "arrow.clockwise" (.button "New address" .plain (if r.changing then none else some (.receive .freshAddress))))
           , Html.symbol "tag" (.button (if label.isNone then "Label this address" else "Edit label") .plain (some (.receive .editLabel)))
           , explorerButton "View address" (m.settings.addressURL a) "address" ] ++
           (r.unconfirmed.map fun (_, amount) =>
             Html.symbol "clock" (Html.tone .warning (body s!"Unconfirmed: +{satsText amount} — awaiting confirmation")))) ] ++
      -- the same page: what to give one person
      personCardSections m ++ errorRows m.shareCard.error
    else if r.error.isNone then [.progress ""]
    else []
  formSheet "Receive" (some .closeSheet) [closeBar "Done" Ids.closeReceiveButton] (content ++ errorRows r.error) inner

/-- PaymentDetailView's "Address label" sheet. -/
def labelSheet (m : Model) (inner : List H) : H :=
  formSheet "Address label" (if m.labelEditor.saving then none else some .closeSheet) [] (labelEditorView m) inner

/-- One person's address and card on a sheet of their own, for "Show the card you made for …" under a saved
recipient: the same rows as on Receive. -/
def shareCardSheet (m : Model) (inner : List H) : H :=
  formSheet (if m.shareCard.forName.trimAscii.isEmpty then "From one person" else s!"From {m.shareCard.forName.trimAscii.copy}")
    (some .closeSheet) [closeBar "Done" Ids.closeShareCardButton]
    (personCardSections m ++ errorRows m.shareCard.error) inner

end WinnowApp
