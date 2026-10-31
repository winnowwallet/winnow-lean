import Std.Sync.Mutex
import Winnow.IO.Http
import WinnowApp.Model
import WinnowApp.Pure
import WinnowApp.Real.RecordsStores

/-! # The records side of the backend (people, labels)

Ports of AppModel's records state and operations (`Sources/WinnowApp/AppModel.swift`: `ownKeyExpression`,
people, labels, the sender lookup) over the stores of `RecordsStores.lean`, plus the derived data AppModel
recomputes in its `didSet`s (`recipientByScript`, `senderByTxid`) and the app's `Records` summary. The
vault, shared-savings, approval and MuSig2 operations went with vaults (upstream 1cf93fb).

Every operation takes what it needs explicitly: the `RecordsStore` (which holds the network, the
directory and the store keys) and the open `Winnow.Wallet` where the wallet's own keys matter. Failures are `RecordsError`s (`RM`); `RM.toIO` turns
one into the `IO.userError` of its description, which is what the screens show.

The store state sits behind one `Std.Mutex`, so reads from another task never see half a mutation. The
caller still serializes mutations (AppModel's `exclusively(.spending)` gate is the caller's). -/

namespace WinnowApp.RecordsReal
open Winnow SwiftJSON
open Tx (BitcoinNetwork)

/-! ## The store -/

structure RecordsState where
  people : PeopleStore := {}
  /-- `peopleStorageNotice`: set when `people.json` could not be read; never blocks boot. -/
  peopleNotice : Option String := none
  /-- The receive-label store of the wallet last asked about (`configureReceiveAddressLabels`). -/
  labels : Option LabelStore := none
  /-- `recipientByScript`, recomputed only after people change (AppModel's `didSet`): each person
  derives `nextPaymentIndex + gapLimit` scripts. -/
  recipientsCache : Option (Array (ByteArray × PersonRecord)) := none
  deriving Inhabited

/-- people.json and receive-labels.json of one network directory. -/
structure RecordsStore where
  network : BitcoinNetwork
  /-- `ApplicationSupport/BTCSwift/<network>/`; none when storage is unreachable. -/
  dir : Option System.FilePath
  keys : StoreKeyVault
  writeData : WriteData := writeAtomically
  state : Std.Mutex RecordsState
  /-- `e2e?.journal(_:fields:)` (test mode's event journal); a no-op otherwise. -/
  journal : String → List (String × String) → IO Unit := fun _ _ => pure ()

namespace RecordsStore

def peoplePath (s : RecordsStore) : Option System.FilePath := s.dir.map (· / "people.json")
def labelsPath (s : RecordsStore) : Option System.FilePath := s.dir.map (· / "receive-labels.json")

/-- Runs `f` on the state under the lock; the state changes only when `f` succeeds. -/
def modify {α} (s : RecordsStore) (f : RecordsState → RM (RecordsState × α)) : RM α :=
  s.state.atomically do
    let st ← get
    let (st', a) ← (f st : RM _)
    set { st' with recipientsCache := none }
    return a

def read (s : RecordsStore) : IO RecordsState := s.state.atomically get

/-- One journal line from inside a records operation. -/
def note (s : RecordsStore) (name : String) (fields : List (String × String)) : RM Unit := RM.io (s.journal name fields)

/-- Re-reads the sealed people file (boot, adopting a wallet, deleting one). Damage is the notice, never
`storageDamaged`. -/
def configure (s : RecordsStore) : IO Unit := do
  let (people, peopleResult) ← PeopleStore.configure s.keys s.peoplePath s.network s.writeData
  let notice := match peopleResult with | .damaged m => some m | _ => none
  s.state.atomically (set ({ people, peopleNotice := notice, labels := none } : RecordsState))

/-- Opens the records of `network` under `dir`, with store keys from `keys`. -/
def «open» (network : BitcoinNetwork) (dir : Option System.FilePath) (keys : StoreKeyVault)
    (writeData : WriteData := writeAtomically) : IO RecordsStore := do
  let s : RecordsStore := { network, dir, keys, writeData, state := ← Std.Mutex.new {} }
  s.configure
  return s

/-- The receive-label store for `walletID`, reopened when the wallet changed. -/
def labelStore (s : RecordsStore) (st : RecordsState) (walletID : String) : IO LabelStore := do
  match st.labels with
  | some l => if l.walletID == walletID then return l else LabelStore.open s.labelsPath walletID s.network
  | none => LabelStore.open s.labelsPath walletID s.network

end RecordsStore

/-! ## The wallet's own keys -/

def formatPath (path : Array UInt32) : String :=
  "/".intercalate (path.toList.map fun step =>
    if step ≥ Keys.HDKey.hardenedOffset then s!"{(step - Keys.HDKey.hardenedOffset).toNat}'" else s!"{step.toNat}")

/-- `ownKeyExpression(multipathSuffix:)`: `[fp/86'/coin'/0']xpub…`, plus `/<0;1>/*` (the key others pay). -/
def ownKeyExpressionOf (d : Descriptor) (multipath : Bool) : RM String := do
  let .tr key := d.expression | throw (.app .noWallet)
  let some origin := key.origin | throw (.app .noWallet)
  let .extended accountKey hdNetwork := key.base | throw (.app .noWallet)
  let base := s!"[{Wallet.hex8 origin.fingerprint}/{formatPath origin.path}]{accountKey.serialized hdNetwork}"
  return if multipath then base ++ "/<0;1>/*" else base

def ownKeyExpression (w : Wallet) (multipath : Bool) : RM String := ownKeyExpressionOf w.descriptor multipath

/-- `ownPersonCard(name:)`: this wallet's account key as the pay-to key. Public material only. -/
def ownPersonCardOf (d : Descriptor) (network : BitcoinNetwork) (name : String) : RM PersonCard := do
  let key ← ownKeyExpressionOf d true
  let payTo ← RM.lift (fun e => .named e.name e.description) (PersonPayTo.ofDescriptor s!"tr({key})" network)
  return PersonCard.make network name (some payTo.text)

def ownPersonCard (w : Wallet) (name : String) : RM PersonCard := ownPersonCardOf w.descriptor w.network name

/-! ## Derived data -/

/-- `recipientByScript`: every script a person could have been paid at so far (the first person wins). -/
def recipientByScript (people : Array PersonRecord) (network : BitcoinNetwork) : Array (ByteArray × PersonRecord) := Id.run do
  let mut seen : Std.HashSet ByteArray := {}
  let mut out := #[]
  for p in people do
    let some payTo := p.payTo | continue
    let scripts := (payTo.scripts (p.nextPaymentIndex + Wallet.gapLimit) network).toOption.getD #[]
    for s in scripts do
      if seen.contains s then continue
      seen := seen.insert s
      out := out.push (s, p)
  return out

/-- `personScripts()`: script → name. -/
def personScripts (people : Array PersonRecord) (network : BitcoinNetwork) : Array (ByteArray × String) :=
  (recipientByScript people network).map fun (s, p) => (s, p.name)

/-! ## The `Records` summary -/

def personSummary (p : PersonRecord) : Person :=
  { id := p.id, name := p.name, payTo := p.payTo.map (·.derivesFreshAddresses),
    nextPaymentIndex := p.nextPaymentIndex.toNat, savedRecipient := p.savedRecipient,
    provenance := p.destinationProvenance }

/-- The app's `Records` from the stores and the open wallet (if any). -/
def summaryOf (s : RecordsStore) (st : RecordsState) (w : Option Wallet) : IO (Records × RecordsState) := do
  let network := s.network
  let (labels, st) ← match w with
    | some w => do
      let l ← s.labelStore st w.id
      pure (some l, { st with labels := some l })
    | none => pure (none, st)
  let recipients := st.recipientsCache.getD (recipientByScript st.people.records network)
  let st := { st with recipientsCache := some recipients }
  let records : Records := {
    people := st.people.records.toList.map personSummary
    senderByTxid := st.people.senderByTxid.toList
    recipientByScript := recipients.toList.map fun (sc, p) => (hex sc, p.id)
    receiveLabels := match labels with
      | some l => l.labels.toList.filterMap fun (sc, note) => (AddressDecoder.address sc network).map (·, note)
      | none => []
    peopleStorageNotice := st.peopleNotice
    receiveLabelStorageNotice := labels.bind (·.notice) }
  return (records, st)

/-- `records`: people, sender and receive labels. -/
def records (s : RecordsStore) (w : Option Wallet) : IO Records := do
  s.state.atomically do
    let (r, st) ← summaryOf s (← get) w
    set st
    return r

/-- `recipientByScript`, from the cache when people have not changed since. -/
def recipients (s : RecordsStore) : IO (Array (ByteArray × PersonRecord)) :=
  s.state.atomically do
    let st ← get
    match st.recipientsCache with
    | some r => return r
    | none =>
      let r := recipientByScript st.people.records s.network
      set { st with recipientsCache := some r }
      return r

/-- A mutation of the state, answered with the fresh `Records`. -/
def mutate (s : RecordsStore) (w : Option Wallet) (f : RecordsState → RM RecordsState) : RM Records := do
  s.modify fun st => do pure (← f st, ())
  RM.io (records s w)

/-! ## Receive labels -/

/-- `setReceiveAddressLabel(_:address:)`: only for the wallet's own watched scripts; empty text removes. -/
def setReceiveLabel (s : RecordsStore) (w : Wallet) (address label : String) : RM Records := do
  let script ← RM.lift (fun e => namedError e.name s.network) (AddressDecoder.scriptPubKey address s.network)
  let watched ← liftWallet s.network w.watchScripts
  unless watched.contains script do throw (.app .noWallet)
  mutate s (some w) fun st => do
    let l ← RM.io (s.labelStore st w.id)
    let l ← l.setLabel s.writeData label address
    return { st with labels := some l }

/-! ## People -/

/-- `PersonPaste.parse`, as the Add-person screen previews it. -/
def parsePaste (network : BitcoinNetwork) (text : String) : RM PastePreview := do
  let p ← liftNamed network (PersonPaste.parse text network)
  return { name := p.name, payTo := p.payTo.map (·.derivesFreshAddresses) }

def withPeople (s : RecordsStore) (w : Option Wallet) (f : PeopleStore → RM PeopleStore) : RM Records :=
  mutate s w fun st => do return { st with people := ← f st.people }

/-- `labelReceivedSender(txid:personID:)` (txid in display hex). -/
def labelSender (s : RecordsStore) (w : Option Wallet) (txid personID : String) : RM Records := do
  let r ← withPeople s w fun ps => ps.labelSender s.keys s.writeData txid personID
  s.note "person.senderLabeled" [("txid", txid), ("personID", personID)]
  return r

/-- `person.added`: the name and what kind of destination. -/
def notePersonAdded (s : RecordsStore) (record : PersonRecord) : RM Unit :=
  s.note "person.added" [("name", record.name),
    ("payToKind", (record.payTo.map fun p => if p.derivesFreshAddresses then "descriptor" else "address").getD "none")]

/-- AddPersonView's save: `addPerson` (+ `labelReceivedSender` when labelling a payment, `labelTxid` in
display hex). -/
def addPerson (s : RecordsStore) (w : Option Wallet) (name : String) (paste : Option String)
    (provenance : Option Provenance) (source : Option String) (labelTxid : Option String) : RM Records := do
  let network := s.network
  let pasted := paste.bind fun t => if (Wire.trimWhitespace t).isEmpty then none else some t
  let parsed ← pasted.mapM fun t => liftNamed network (PersonPaste.parse t network)
  let id ← RM.io uuidString
  match labelTxid with
  | some txid =>
    -- Two steps, as AppModel takes them: the person is saved even when the label then fails.
    let payTo := parsed.bind (·.payTo)
    let record ← s.modify fun st => do
      let (ps, record) ← st.people.add s.keys s.writeData id name payTo (if payTo.isSome then provenance else none)
        (if payTo.isSome then source else none)
      return ({ st with people := ps }, record)
    notePersonAdded s record
    labelSender s w txid record.id
  | none =>
    let some p := parsed | throw (namedError "empty" network)
    if p.payTo.isNone then throw (namedError "unrecognised" network)
    let record ← s.modify fun st => do
      let (ps, record) ← st.people.add s.keys s.writeData id name p.payTo provenance source
      return ({ st with people := ps }, record)
    notePersonAdded s record
    RM.io (records s w)

/-- `attachDestination(id:payTo:provenance:source:)` from a pasted address or card. -/
def attachDestination (s : RecordsStore) (w : Option Wallet) (personID paste : String) (provenance : Provenance)
    (source : Option String) : RM Records := do
  let p ← liftNamed s.network (PersonPaste.parse paste s.network)
  let some payTo := p.payTo | throw (.app .personCannotBePaid)
  withPeople s w fun ps => ps.attachDestination s.keys s.writeData personID payTo provenance source

def updateRecipient (s : RecordsStore) (w : Option Wallet) (personID : String) (name : Option String) (saved : Bool) :
    RM Records :=
  withPeople s w fun ps => do return (← ps.updateRecipient s.keys s.writeData personID name saved).1

/-- `PeopleStore.remove(id:)`: forgets the person and every sender label naming them. -/
def removePerson (s : RecordsStore) (w : Option Wallet) (personID : String) : RM Records :=
  withPeople s w fun ps => ps.remove s.keys s.writeData personID

def removeSenderLabel (s : RecordsStore) (w : Option Wallet) (txid : String) : RM Records :=
  withPeople s w fun ps => RM.io (ps.removeSenderLabel s.keys s.writeData txid)

/-- `advancePersonPaymentIndex(id:past:)`: best effort, as AppModel calls it. -/
def advancePersonPaymentIndex (s : RecordsStore) (w : Option Wallet) (personID : String) (index : UInt32) : IO Records := do
  discard <| (withPeople s w fun ps => ps.advancePaymentIndex s.keys s.writeData personID index).run
  records s w

/-- `nextPaymentAddress(for:)`: peeked, never advanced here. -/
def nextPaymentAddress (s : RecordsStore) (personID : String) : RM (String × UInt32) := do
  let st ← RM.io s.read
  let some p := st.people.record? personID | throw (.people .unknownPerson)
  let some payTo := p.payTo | throw (.app .personCannotBePaid)
  return (← liftNamed s.network (payTo.addressAt p.nextPaymentIndex s.network), p.nextPaymentIndex)

/-! ## The sender lookup -/

def maximumLookupBytes : Nat := 2 * 1024 * 1024

def lookupFormatError : RecordsError := .lookup "The explorer answered in a format Winnow does not understand."

/-- `EsploraSenderLookup.parseFundingAddresses`: a top-level object with a `vin` array of objects, each
optionally carrying `prevout.scriptpubkey_address`; the distinct addresses in input order. -/
def parseFundingAddresses (data : ByteArray) (network : BitcoinNetwork) (expectedTxid : Option String) :
    RM (List String) := do
  unless data.size ≤ maximumLookupBytes do throw (.lookup "Explorer response too large.")
  let some text := String.fromUTF8? data | throw lookupFormatError
  let some (.obj root) := parse? text | throw lookupFormatError
  let some (.arr vin) := SwiftJSON.lookup root "vin" | throw lookupFormatError
  let inputs ← vin.mapM fun v => match v with | .obj kvs => pure kvs | _ => throw lookupFormatError
  unless inputs.size ≤ 10_000 do throw lookupFormatError
  if let some expected := expectedTxid then
    unless SwiftJSON.lookup root "txid" == some (.str expected) do
      throw (.lookup "The explorer returned a different transaction.")
  let mut out : Array String := #[]
  for input in inputs do
    let some (.obj prevout) := SwiftJSON.lookup input "prevout" | continue
    let some (.str address) := SwiftJSON.lookup prevout "scriptpubkey_address" | continue
    if address.isEmpty || out.contains address then continue
    discard <| RM.lift (fun e => namedError e.name network) (AddressDecoder.scriptPubKey address network)
    out := out.push address
  return out.toList

/-- One GET of `{baseURL}/tx/{txid}` through `get url maximumBytes` (the routed HTTP client); `txid` in
display hex. The consent check (network generation) is the caller's. -/
def lookupSender (get : String → Nat → IO ByteArray) (network : BitcoinNetwork) (txid baseURL : String) :
    RM (List String) := do
  let some raw := Wire.dataOfHex? txid | throw (.lookup "Invalid transaction ID.")
  unless raw.size == 32 do throw (.lookup "Invalid transaction ID.")
  let url := appendPath baseURL ["tx", txid]
  let data ← RM.io (get url maximumLookupBytes)
  parseFundingAddresses data network (some txid)

/-- The getter over the I/O area's `RoutedHTTPClient`. -/
def routedGetter (c : Winnow.IO.RoutedHTTPClient) : String → Nat → IO ByteArray := fun url max =>
  (c.get url max).toIO

end WinnowApp.RecordsReal
