import WinnowApp.Home

/-! RecipientsView.swift: SavedRecipientsView, and AddPersonView in all its modes — a new recipient, a
payment's address, a rename, a destination for someone without one, and the
sender of a received payment (a saved person, the funding addresses the payment reveals, or the
consented explorer lookup). -/

namespace WinnowApp
open LeanNative

def fundingWarning : String :=
  "A funding address is unverified as a destination for this person. Exchanges, coinjoins and shared wallets can make it misleading. Select one only after checking with the person. Sending to it reuses an address; ask for a fresh address or payment card."

def lookupDisclosure : String := "The explorer receives this transaction ID and your IP address over a direct connection."

def PersonForm.person? (f : PersonForm) (m : Model) : Option Person := f.mode.personID.bind m.person?
def PersonForm.labelingSender (f : PersonForm) : Bool := f.mode.txid.isSome && f.mode.personID.isNone
/-- `txid != nil && person?.payTo == nil` (true when labelling a new sender too). -/
def PersonForm.choosingFunding (f : PersonForm) (m : Model) : Bool :=
  f.mode.txid.isSome && ((f.person? m).bind (·.payTo)).isNone

def PersonForm.effectiveName (f : PersonForm) : String :=
  let t := f.name.trimAscii.copy
  if t.isEmpty then (f.parsed.bind (·.name)).getD "" else t

def PersonForm.canSave (f : PersonForm) (m : Model) : Bool :=
  if f.saving || f.effectiveName.isEmpty then false
  else if !f.pasted.trimAscii.isEmpty && f.parsed.isNone then false
  else if (f.person? m).isSome then true
  else if f.labelingSender then true
  else (f.parsed.bind (·.payTo)).isSome

def PersonForm.provenance (f : PersonForm) : Option Provenance :=
  if (f.parsed.bind (·.payTo)).isNone then none else
  match f.selectedFunding with
  | some (a, p) => if f.pasted == a then some p else some .supplied
  | none => some .supplied

def PersonForm.source (f : PersonForm) : Option String :=
  match f.provenance with
  | some .localFunding => f.mode.txid
  | some .explorerFunding => f.inferredSource
  | _ => none

def PersonForm.title (f : PersonForm) (m : Model) : String :=
  if f.labelingSender then "Save sender" else
  match f.person? m with
  | some p =>
    if p.payTo.isNone then s!"Add destination for {p.name}"
    else if p.isSavedRecipient then "Rename recipient"
    else "Save recipient"
  | none => "Save recipient"

def Model.setPersonPasted (m : Model) (s : String) : Model × List Cmd :=
  ({ m with person := { m.person with pasted := s, parsed := none, error := none } },
   if s.trimAscii.isEmpty then [] else [.parsePaste m.generation s])

def stepPeople (msg : PeopleMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  let f := m.person
  match msg with
  | .openAdd mode address => m.openPerson mode address
  | .setName s => ({ m with person := { f with name := s } }, [])
  | .setPasted s => m.setPersonPasted s
  | .paste => (m, [.paste .person])
  | .chooseSaved pid => match f.mode.txid with
    | some t => ({ m with person := { f with saving := true } }, [.labelSender g t pid])
    | none => (m, [])
  | .chooseFunding a p =>
    let (m', cs) := m.setPersonPasted a
    ({ m' with person := { m'.person with selectedFunding := some (a, p) } }, cs)
  | .askInfer => ({ m with person := { f with lookupConsent := some (m.settings.esploraBaseURL, g) }, confirm := some .inferSender }, [])
  | .infer =>
    let m := { m with confirm := none }
    match f.lookupConsent, f.mode.txid with
    | some (base, gen), some t =>
      -- the consent is tied to the explorer and networking generation it was given in
      if gen != g || base != m.settings.esploraBaseURL || !m.active then
        ({ m with person := { f with error := some "The network connection changed. Review the lookup warning again." } }, [])
      else ({ m with person := { f with inferring := true, error := none } }, [.lookupSender g t base])
    | _, _ => (m, [])
  | .save =>
    if !f.canSave m then (m, []) else
    let m' := { m with person := { f with saving := true, error := none } }
    let payable := (f.parsed.bind (·.payTo)).isSome
    match f.person? m with
    | some p =>
      let attach := if p.payTo.isNone && payable then some (f.pasted, f.provenance.getD .supplied, f.source) else none
      (m', [.editPerson g p.id f.effectiveName attach])
    | none =>
      let paste := if f.pasted.trimAscii.isEmpty then none else some f.pasted
      if f.labelingSender then
        (m', [.addPerson g f.effectiveName (if payable then paste else none) f.provenance f.source f.mode.txid])
      else (m', [.addPerson g f.effectiveName paste none none none])
  | .choose pid =>
    match m.person? pid with
    | some p =>
      if p.payTo.isNone then m.openPerson { personID := some pid } ""
      else
        let (m', cs) := m.closeSheet .savedRecipients
        let m' := { m' with send := { m'.send with inputs := { m'.send.inputs with personID := some pid, destination := "" },
                                                    preview := none, error := none } }
        (m', cs)
    | none => (m, [])
  | .rename pid => m.openPerson { personID := some pid } ""
  | .remove pid => ({ m with recipientsError := none }, [.updateRecipient g pid none false "recipients"])

/-! ## View -/

def addPersonSheet (m : Model) (inner : List H) : H :=
  let f := m.person
  let host := m.settings.explorerHost
  let person := f.person? m
  let candidates := match f.mode.txid.bind m.historyItem? with
    | some h => senderCandidates h
    | none => []
  let choosing := f.choosingFunding m
  formSheet (f.title m) (if f.saving then none else some .closeSheet) [closeBar "Cancel"]
    ([ .section "" ""
         ([.input .plain "" "Name" f.name (fun s => .people (.setName s)) none] ++
          (if (person.bind (·.payTo)).isNone then
            [ .input .multiline "" "Paste an address or card" f.pasted
                (fun s => .people (.setPasted s)) none
            , .button "Paste from clipboard" .plain (some (.people .paste)) ]
           else [])) ] ++
     (if f.labelingSender && !m.records.people.isEmpty then
       [.section "Or choose someone saved" ""
         (m.records.people.map fun p => .button p.name .plain (if f.saving then none else some (.people (.chooseSaved p.id))))]
      else []) ++
     (if choosing && !candidates.isEmpty then
       [.section "Funding addresses this payment reveals" fundingWarning
         (candidates.map fun (_, a) => .button a .plain (some (.people (.chooseFunding a .localFunding))))]
      else []) ++
     (if choosing && candidates.isEmpty then
       [.section "" s!"The locally stored payment does not reveal a funding address. You can request unverified funding addresses from {host} after reviewing what the lookup discloses."
         [.button (if f.inferring then "Looking up…" else s!"Find funding addresses with {host}") .plain
            (if f.inferring then none else some (.people .askInfer))]]
      else []) ++
     (if f.inferredAddresses.isEmpty then [] else
       [.section s!"Funded by, according to {host}" fundingWarning
         (f.inferredAddresses.map fun a => .button a .plain (some (.people (.chooseFunding a .explorerFunding))))]) ++
     (match f.parsed, person with
      | some p, none =>
        [.section "" ""
          (match p.payTo with
            | some fresh => [caption (if fresh then "Fresh address each payment" else "Uses this same address each time")]
            | none => [])]
      | _, _ => []) ++
     errorRows f.error ++
     [.section "" "" [.button (if f.saving then "Saving…" else "Save") .primary (if f.canSave m then some (.people .save) else none)]])
    inner

def savedRecipientsSheet (m : Model) (inner : List H) : H :=
  let shown := m.records.people.filter (·.savedRecipient != some false)
  let locked := m.records.peopleStorageNotice.isSome
  formSheet "Saved recipients" (some .closeSheet)
    [ closeBar "Done"
    , .toolbar [Html.symbol "plus" (.button "Add" .plain (if locked then none else some (.people (.openAdd {} ""))))] ]
    (errorRows (m.records.peopleStorageNotice <|> m.recipientsError) ++
     (if shown.isEmpty then [caption "Save a recipient from a payment in Wallet, or add an address or card here."] else []) ++
     (shown.map fun p =>
        .row [ .button (if p.payTo.isNone then s!"{p.name} — add destination" else p.name) .plain (some (.people (.choose p.id)))
             , .spacer
             , .button "Rename" .plain (some (.people (.rename p.id)))
             , .button "Remove" .destructive (some (.people (.remove p.id))) ])) inner

end WinnowApp
