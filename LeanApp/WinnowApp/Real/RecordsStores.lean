import Std.Data.HashSet
import WinnowApp.Real.RecordsSeal

/-! # The records stores (ports of `PeopleStore.swift` and `ReceiveAddressLabelStore.swift`)

Each Swift store is an actor (or a main-actor class) around an array; here each is an immutable value and
every mutation returns the next value, so "apply to a copy, validate, persist, adopt the copy only when
every step succeeded" is simply "return the new store, or fail and keep the old one". `RecordsStore`
(`Records.lean`) holds them behind one mutex. (`VaultStore` went with vaults, upstream 1cf93fb.)

Files, byte for byte with the Swift app:

* `people.json`: the sealed `{"people":[…],"senderByTxid":{…}}` envelope with sorted keys and unescaped
  slashes (exactly the Swift bytes); a bare `[PersonRecord]` array (the older shape) still reads, and a
  record's `signerKey` (written before vaults were removed) is ignored.
* `receive-labels.json`: unsealed `{"labels":{script hex: note},"network":…,"version":1,"walletID":…}`,
  sorted keys (exactly the Swift bytes). -/

namespace WinnowApp.RecordsReal
open Winnow SwiftJSON
open Tx (BitcoinNetwork)

/-- What opening a store found (`PeopleStorageOpenResult`). -/
inductive OpenResult where
  | missing
  | loaded
  | damaged (message : String)
  deriving Repr, BEq, Inhabited

def isSealFailure : RecordsError → Bool
  | .seal _ => true
  | _ => false

def outpointKey (txid : ByteArray) (vout : UInt32) : String := hex txid ++ ":" ++ toString vout

/-! ## People -/

/-- `PersonRecord`: a saved recipient. Public keys only. -/
structure PersonRecord where
  /-- Opaque; a UUID string. -/
  id : String
  name : String
  payTo : Option PersonPayTo := none
  nextPaymentIndex : UInt32 := 0
  savedRecipient : Option Bool := none
  destinationProvenance : Option Provenance := none
  destinationSource : Option String := none
  deriving Inhabited, BEq

namespace PersonRecord

def hasUnverifiedFundingDestination (p : PersonRecord) : Bool :=
  p.destinationProvenance == some .localFunding || p.destinationProvenance == some .explorerFunding
def derivesFreshAddresses (p : PersonRecord) : Bool := (p.payTo.map (·.derivesFreshAddresses)).getD false
def isSavedRecipient (p : PersonRecord) : Bool := p.payTo.isSome && p.savedRecipient != some false

def provenanceRaw : Provenance → String
  | .supplied => "supplied" | .localFunding => "localFunding" | .explorerFunding => "explorerFunding"

def provenanceOfJV (v : JV) : D Provenance := do
  match ← asString v with
  | "supplied" => pure .supplied
  | "localFunding" => pure .localFunding
  | "explorerFunding" => pure .explorerFunding
  | _ => dataCorrupted

def toJV (p : PersonRecord) : JV :=
  obj [("id", some (.str p.id)), ("name", some (.str p.name)), ("payTo", p.payTo.map PersonPayTo.toJV),
    ("nextPaymentIndex", some (ofInt p.nextPaymentIndex.toNat)),
    ("savedRecipient", p.savedRecipient.map .bool),
    ("destinationProvenance", p.destinationProvenance.map (.str ∘ provenanceRaw)),
    ("destinationSource", p.destinationSource.map .str)]

/-- Synthesized `init(from:)`: `id`, `name` and `nextPaymentIndex` required (property defaults are not
used by the synthesized decoder), the optionals `decodeIfPresent`; any other key (a `signerKey` from
before vaults went) is ignored. -/
def ofJV (v : JV) : D PersonRecord := do
  let kvs ← asObject v
  let id ← key kvs "id" asString
  let name ← key kvs "name" asString
  let payTo ← keyIfPresent kvs "payTo" PersonPayTo.ofJV
  let nextPaymentIndex ← key kvs "nextPaymentIndex" asUInt32
  let savedRecipient ← keyIfPresent kvs "savedRecipient" asBool
  let destinationProvenance ← keyIfPresent kvs "destinationProvenance" provenanceOfJV
  let destinationSource ← keyIfPresent kvs "destinationSource" asString
  return { id, name, payTo, nextPaymentIndex, savedRecipient, destinationProvenance, destinationSource }

end PersonRecord

/-- `PeopleStore`. -/
structure PeopleStore where
  records : Array PersonRecord := #[]
  /-- Txid display hex → person id. -/
  senderByTxid : Array (String × String) := #[]
  path : Option System.FilePath := none
  network : BitcoinNetwork := .signet
  isDamaged : Bool := false
  deriving Inhabited

namespace PeopleStore

def maximumPeople : Nat := 1_000
def maximumSenderLabels : Nat := 1_000
/-- Leaves room below the hardened offset for the two indices a payment advances past the one it derived. -/
def maximumNextIndex : UInt32 := 10_000 - 2
def maximumFileBytes : Nat := 4 * 1_024 * 1_024
def maximumSourceLength : Nat := 256
def storeName : String := "people"

def damagedStorageMessage : String :=
  "Winnow could not read the saved-recipient file. It has been left untouched. You can still send to an address; saved recipients cannot be changed until the file is readable again."

def unverifiedStorageMessage : String :=
  "The saved-recipient file could not be verified: it was not written by Winnow on this device, or its protected key is gone. It has been left untouched. You can still send to an address; saved recipients cannot be changed until the file verifies again."

def messageFor (e : RecordsError) : String := if isSealFailure e then unverifiedStorageMessage else damagedStorageMessage

def invalid {α} (reason : String) : RM α := throw (.people (.invalidState reason))

def lookupLabel (labels : Array (String × String)) (k : String) : Option String := (labels.find? (·.1 == k)).map (·.2)

def setLabel (labels : Array (String × String)) (k : String) (v : Option String) : Array (String × String) :=
  let rest := labels.filter (·.1 != k)
  match v with | some x => rest.push (k, x) | none => rest

def normalizedName (name : String) : RM String := do
  let some n := DisplayName.normalized name | invalid "a person needs a short, single-line name"
  return n

def requireSource (source : Option String) : RM Unit := do
  let some s := source | return
  unless Characters.count s ≤ maximumSourceLength && (DisplayName.normalized s).isSome do
    invalid "a destination source must be short and single-line"

def payIdentity (p : PersonPayTo) (network : BitcoinNetwork) : RM ByteArray := liftNamed network (p.identity network)

/-- The existing person who already holds `candidate`'s key (compared as derived material). -/
def firstSharingAKey (candidate : PersonRecord) (others : Array PersonRecord) (network : BitcoinNetwork) :
    RM (Option PersonRecord) := do
  let some payTo := candidate.payTo | return none
  let pid ← payIdentity payTo network
  for other in others do
    if let some op := other.payTo then
      if (← payIdentity op network) == pid then return some other
  return none

def validateShape (r : PersonRecord) : RM Unit := do
  unless DisplayName.normalized r.name == some r.name do invalid "a person has no usable name"
  requireSource r.destinationSource
  unless r.nextPaymentIndex ≤ maximumNextIndex do invalid "payment index is out of range"

def validatePayTo (r : PersonRecord) (network : BitcoinNetwork) (seen : Std.HashSet ByteArray) : RM (Std.HashSet ByteArray) := do
  let some payTo := r.payTo | return seen
  let canonical ← match payTo with
    | .descriptor t => RM.lift (fun e => .named e.name e.description) (PersonPayTo.ofDescriptor t network)
    | .address t => liftNamed network (PersonPayTo.ofAddress t network)
    | .silentPayment t => liftNamed network ((PersonPayTo.ofSilentPayment t network).mapError (·.name))
  unless canonical == payTo do invalid "pay-to key is not in canonical form"
  let id ← payIdentity payTo network
  if seen.contains id then invalid "two people share a pay-to key"
  return seen.insert id

def isHexTxid (s : String) : Bool := s.length == 64 && (Wire.dataOfHex? s).isSome

def validate (records : Array PersonRecord) (senderByTxid : Array (String × String)) (network : BitcoinNetwork) : RM Unit := do
  unless records.size ≤ maximumPeople do invalid "too many people"
  unless senderByTxid.size ≤ maximumSenderLabels do invalid "too many sender labels"
  for (t, _) in senderByTxid do
    unless isHexTxid t do invalid "a sender label has an invalid transaction id"
  let mut ids : Std.HashSet String := {}
  let mut pays : Std.HashSet ByteArray := {}
  for r in records do
    if ids.contains r.id then invalid "duplicate person identifier"
    ids := ids.insert r.id
    validateShape r
    pays ← validatePayTo r network pays

def labelsJV (labels : Array (String × String)) : JV := .obj (labels.map fun (k, v) => (k, .str v))

def encode (records : Array PersonRecord) (senderByTxid : Array (String × String)) : ByteArray :=
  (writeUnescaped (.obj #[("people", .arr (records.map PersonRecord.toJV)), ("senderByTxid", labelsJV senderByTxid)])).toUTF8

/-- `[String: String]`: an object of strings (a repeated key keeps the last value). -/
def asStringMap (v : JV) : D (Array (String × String)) := do
  let kvs ← asObject v
  let mut out : Array (String × String) := #[]
  for (k, x) in kvs do
    out := setLabel out k (some (← asString x))
  return out

def decodeEnvelope (v : JV) : D (Array PersonRecord × Array (String × String)) := do
  let kvs ← asObject v
  let people ← key kvs "people" (asArray PersonRecord.ofJV)
  let labels := (← keyIfPresent kvs "senderByTxid" asStringMap).getD #[]
  return (people, labels)

/-- The envelope, or the older bare array of people (without labels). -/
def decodePayload (payload : ByteArray) : RM (Array PersonRecord × Array (String × String)) := do
  let some text := String.fromUTF8? payload | throw (.named "dataCorrupted" "The people file is not valid JSON.")
  match decodeText text decodeEnvelope with
  | .ok r => pure r
  | .error _ =>
    let people ← RM.lift (fun e => .named e "The people file could not be decoded.") (decodeText text (asArray PersonRecord.ofJV))
    return (people, #[])

def persist (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) : RM Unit := do
  let some p := s.path | return
  ({ store := storeName, keys } : StoreSeal).write (encode s.records s.senderByTxid) s.network p writeData

/-- `configure(storageURL:network:)`: damage is reported and refuses mutations; the app carries on. -/
def configure (keys : StoreKeyVault) (path : Option System.FilePath) (network : BitcoinNetwork)
    (writeData : WriteData := writeAtomically) : IO (PeopleStore × OpenResult) := do
  let empty : PeopleStore := { path, network }
  let some p := path | return (empty, .missing)
  -- a store the Swift app left is set aside and starts empty; if that fails, it reads as damage below
  discard <| (({ store := storeName, keys } : StoreSeal).setAsideSwiftEra network p).run
  unless ← fileExists p do return (empty, .missing)
  let attempt : RM (PeopleStore × Bool) := do
    let data ← boundedRead p maximumFileBytes (.people (.invalidState "people file too large"))
    let (payload, predates) ← ({ store := storeName, keys } : StoreSeal).read data network
    let (people, labels) ← decodePayload payload
    validate people labels network
    return ({ empty with records := people, senderByTxid := labels }, predates)
  match ← attempt.run with
  | .ok (s, predates) =>
    if predates then discard <| (s.persist keys writeData).run
    return (s, .loaded)
  | .error e => return ({ empty with isDamaged := true }, .damaged (messageFor e))

def record? (s : PeopleStore) (id : String) : Option PersonRecord := s.records.find? (·.id == id)

def sender? (s : PeopleStore) (txidHex : String) : Option PersonRecord :=
  (lookupLabel s.senderByTxid txidHex).bind s.record?

/-- `mutate`: validate, persist, adopt; labels naming a removed person are pruned. -/
def mutate (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (candidate : Array PersonRecord) : RM PeopleStore := do
  let surviving : Std.HashSet String := candidate.foldl (fun a p => a.insert p.id) {}
  let labels := s.senderByTxid.filter fun (_, pid) => surviving.contains pid
  validate candidate labels s.network
  let next := { s with records := candidate, senderByTxid := labels }
  next.persist keys writeData
  return next

def mutateLabels (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (labels : Array (String × String)) :
    RM PeopleStore := do
  validate s.records labels s.network
  let next := { s with senderByTxid := labels }
  next.persist keys writeData
  return next

def requireReadable (s : PeopleStore) : RM Unit := do
  if s.isDamaged then throw (.people .damaged)

/-- `updateRecipient(id:name:saved:)`: presentation only. -/
def updateRecipient (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) (name : Option String)
    (saved : Bool) : RM (PeopleStore × PersonRecord) := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | throw (.people .unknownPerson)
  let normalized ← name.mapM normalizedName
  let next ← s.mutate keys writeData (s.records.modify i fun r =>
    { r with name := normalized.getD r.name, savedRecipient := some saved })
  return (next, next.records[i]!)

/-- `add(name:payTo:provenance:source:)`; `id` is the new record's UUID. -/
def add (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) (name : String)
    (payTo : Option PersonPayTo) (provenance : Option Provenance := none)
    (source : Option String := none) : RM (PeopleStore × PersonRecord) := do
  s.requireReadable
  let trimmed ← normalizedName name
  requireSource source
  let candidate : PersonRecord := { id, name := trimmed, payTo, destinationProvenance := provenance,
                                    destinationSource := source }
  if let some existing ← firstSharingAKey candidate s.records s.network then
    if !existing.isSavedRecipient && payTo.isSome && existing.payTo == payTo then
      return ← s.updateRecipient keys writeData existing.id (some trimmed) true
    throw (.people (.duplicate existing.name))
  unless s.records.size < maximumPeople do throw (.people .tooMany)
  let next ← s.mutate keys writeData (s.records.push candidate)
  return (next, candidate)

/-- `remove(id:)`: the person and every sender label naming them. -/
def remove (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) : RM PeopleStore := do
  s.requireReadable
  unless s.records.any (·.id == id) do throw (.people .unknownPerson)
  s.mutate keys writeData (s.records.filter (·.id != id))

/-- `attachDestination(id:payTo:provenance:source:)`: only a name-only contact gains a destination. -/
def attachDestination (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) (payTo : PersonPayTo)
    (provenance : Provenance) (source : Option String := none) : RM PeopleStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | invalid "only a name-only contact can attach a destination"
  unless s.records[i]!.payTo.isNone do invalid "only a name-only contact can attach a destination"
  requireSource source
  let candidate := { s.records[i]! with payTo := some payTo }
  if let some dup ← firstSharingAKey candidate (s.records.filter (·.id != id)) s.network then
    throw (.people (.duplicate dup.name))
  s.mutate keys writeData (s.records.modify i fun r =>
    { r with payTo := some payTo, destinationProvenance := some provenance, destinationSource := source,
             savedRecipient := some true })

/-- `advancePaymentIndex(id:past:)`: monotonic. -/
def advancePaymentIndex (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) (index : UInt32) :
    RM PeopleStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | throw (.people .unknownPerson)
  let next := index + 1
  unless next > s.records[i]!.nextPaymentIndex do return s
  s.mutate keys writeData (s.records.modify i fun r => { r with nextPaymentIndex := next })

/-- `labelSender(txidHex:personID:)`. -/
def labelSender (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (txidHex personID : String) : RM PeopleStore := do
  s.requireReadable
  unless s.records.any (·.id == personID) do throw (.people .unknownPerson)
  unless (lookupLabel s.senderByTxid txidHex).isSome || s.senderByTxid.size < maximumSenderLabels do
    throw (.people .tooMany)
  s.mutateLabels keys writeData (setLabel s.senderByTxid txidHex (some personID))

/-- `removeSenderLabel(txidHex:)`: best effort (a failed write keeps the label). -/
def removeSenderLabel (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (txidHex : String) : IO PeopleStore := do
  if (lookupLabel s.senderByTxid txidHex).isNone then return s
  match ← (s.mutateLabels keys writeData (setLabel s.senderByTxid txidHex none)).run with
  | .ok n => return n
  | .error _ => return s

/-! ### Backup (`PeopleStore.Backup`, for the encrypted iCloud copy) -/

/-- `PeopleStore.Backup`: the file's payload, people and sender labels. -/
structure Backup where
  people : Array PersonRecord
  /-- Txid display hex → person id (a Swift dictionary: order carries no meaning). -/
  senderByTxid : Array (String × String) := #[]
  deriving Inhabited

namespace Backup

private def sortedLabels (labels : Array (String × String)) : Array (String × String) :=
  (labels.toList.mergeSort fun a b => !(b.1 < a.1)).toArray

/-- Swift's `==`: the people in order, the labels as a dictionary. -/
def same (a b : Backup) : Bool := a.people == b.people && sortedLabels a.senderByTxid == sortedLabels b.senderByTxid

instance : BEq Backup := ⟨same⟩

def toJV (b : Backup) : JV := .obj #[("people", .arr (b.people.map PersonRecord.toJV)), ("senderByTxid", labelsJV b.senderByTxid)]

/-- `init(from:)`: `people` required, `senderByTxid` absent in older files. -/
def ofJV (v : JV) : D Backup := do
  let (people, senderByTxid) ← decodeEnvelope v
  return { people, senderByTxid }

end Backup

/-- `backup()`: what the store holds; refused while the file is damaged. -/
def backup (s : PeopleStore) : RM Backup := do
  s.requireReadable
  return { people := s.records, senderByTxid := s.senderByTxid }

/-- `validateBackup(_:network:)`: the file's own rules, every sender label naming a person in the backup,
and the file's byte ceiling. -/
def validateBackup (b : Backup) (network : BitcoinNetwork) : RM Unit := do
  validate b.people b.senderByTxid network
  let ids : Std.HashSet String := b.people.foldl (fun a p => a.insert p.id) {}
  unless b.senderByTxid.all (fun (_, id) => ids.contains id) && (write b.toJV).utf8ByteSize ≤ maximumFileBytes do
    invalid "invalid cloud address book"

/-- `planRestore(_:)`: keeps the contacts already on this device (matched by id, else by a shared key),
never rewinds a recipient's payment counter, and remaps the incoming sender labels onto the kept ids
without replacing a label this device already has. -/
def planRestore (s : PeopleStore) (incoming : Backup) : RM Backup := do
  s.requireReadable
  validateBackup incoming s.network
  let mut merged := s.records
  let mut ids : Array (String × String) := #[]
  for person in incoming.people do
    let existing ← match merged.find? (·.id == person.id) with
      | some e => pure (some e)
      | none => firstSharingAKey person merged s.network
    match existing with
    | some e =>
      let some i := merged.findIdx? (·.id == e.id) | continue
      ids := setLabel ids person.id (some e.id)
      let ours ← e.payTo.mapM (payIdentity · s.network)
      let theirs ← person.payTo.mapM (payIdentity · s.network)
      if ours == theirs then
        merged := merged.modify i fun r => { r with nextPaymentIndex := max e.nextPaymentIndex person.nextPaymentIndex }
    | none =>
      merged := merged.push person
      ids := setLabel ids person.id (some person.id)
  let mut labels := s.senderByTxid
  for (txid, id) in incoming.senderByTxid do
    if (lookupLabel labels txid).isNone then
      if let some mapped := lookupLabel ids id then labels := setLabel labels txid (some mapped)
  let result : Backup := { people := merged, senderByTxid := labels }
  validateBackup result s.network
  return result

/-- `restore(_:)`: replaces the store's contents with a validated backup, persisted before adopted. -/
def restore (s : PeopleStore) (keys : StoreKeyVault) (writeData : WriteData) (b : Backup) : RM PeopleStore := do
  s.requireReadable
  validateBackup b s.network
  let next := { s with records := b.people, senderByTxid := b.senderByTxid }
  next.persist keys writeData
  return next

end PeopleStore

/-! ## Receive address labels -/

/-- `ReceiveAddressLabelStore`: notes about this wallet's own addresses (one wallet, one network). -/
structure LabelStore where
  walletID : String
  network : BitcoinNetwork
  path : Option System.FilePath
  /-- Canonical script → note. -/
  labels : Array (ByteArray × String) := #[]
  notice : Option String := none
  deriving Inhabited

namespace LabelStore

def maximumLabels : Nat := 10_000
def maximumLabelLength : Nat := 120
def maximumFileBytes : Nat := 4 * 1_024 * 1_024

/-- `normalizedLabel(_:)`: trimmed, at most 120 characters (480 UTF-8 bytes), no control characters or
newlines. Empty is allowed (it removes a label). -/
def normalizedLabel (text : String) : Except LabelStorageError String := do
  let label := Wire.trimWhitespace text
  unless Characters.count label ≤ maximumLabelLength && label.utf8ByteSize ≤ maximumLabelLength * 4 &&
      !label.toList.any DisplayName.isControlOrNewline do
    throw .invalidLabel
  return label

def readLabels (path : System.FilePath) (walletID : String) (network : BitcoinNetwork) : RM (Array (ByteArray × String)) := do
  let damaged : RecordsError := .labels .damaged
  let data ← boundedRead path maximumFileBytes damaged
  let some text := String.fromUTF8? data | throw damaged
  let payload : D (Int × String × String × Array (String × String)) := decodeText text fun v => do
    let kvs ← asObject v
    return (← key kvs "version" asInt, ← key kvs "walletID" asString, ← key kvs "network" asString,
            ← key kvs "labels" PeopleStore.asStringMap)
  let .ok (version, wid, net, labels) := payload | throw damaged
  unless version == 1 && wid == walletID && net == networkRaw network && labels.size ≤ maximumLabels do throw damaged
  let mut out : Array (ByteArray × String) := #[]
  for (k, label) in labels do
    let some script := Wire.dataOfHex? k | throw damaged
    unless hex script == k && (AddressDecoder.address script network).isSome &&
        (normalizedLabel label).toOption == some label && !label.isEmpty do throw damaged
    out := (out.filter (·.1 != script)).push (script, label)
  return out

/-- `init(storageURL:walletID:network:)`. -/
def «open» (path : Option System.FilePath) (walletID : String) (network : BitcoinNetwork) : IO LabelStore := do
  let s : LabelStore := { walletID, network, path }
  let some p := path | return { s with notice := some (RecordsError.labels .unavailable).description }
  unless ← fileExists p do return s
  match ← (readLabels p walletID network).run with
  | .ok labels => return { s with labels }
  | .error _ => return { s with notice := some (RecordsError.labels .damaged).description }

def label? (s : LabelStore) (script : ByteArray) : Option String := (s.labels.find? (·.1 == script)).map (·.2)

def encode (s : LabelStore) (labels : Array (ByteArray × String)) : ByteArray :=
  (write (.obj #[("version", ofInt 1), ("walletID", .str s.walletID), ("network", .str (networkRaw s.network)),
    ("labels", .obj (labels.map fun (k, v) => (hex k, .str v)))])).toUTF8

/-- `setLabel(_:address:)`: empty text removes a label; the live view changes only after the write. -/
def setLabel (s : LabelStore) (writeData : WriteData) (text address : String) : RM LabelStore := do
  if s.notice.isSome then throw (.labels .damaged)
  let some p := s.path | throw (.labels .unavailable)
  let script ← RM.lift (fun e => namedError e.name s.network) (AddressDecoder.scriptPubKey address s.network)
  let label ← RM.lift .labels (normalizedLabel text)
  let rest := s.labels.filter (·.1 != script)
  let updated := if label.isEmpty then rest else rest.push (script, label)
  unless updated.size ≤ maximumLabels do throw (.labels .full)
  let data := s.encode updated
  unless data.size ≤ maximumFileBytes do throw (.labels .full)
  RM.io (writeData data p)
  return { s with labels := updated }

/-! ### Backup (for the encrypted iCloud copy) -/

/-- `validatedBackup(_:network:)`: canonical script hex that makes an address on the network, each with a
non-empty normalized note; at most `maximumLabels` (`full`), anything else `damaged`. -/
def validatedBackup (labels : Array (String × String)) (network : BitcoinNetwork) : RM (Array (ByteArray × String)) := do
  unless labels.size ≤ maximumLabels do throw (.labels .full)
  let mut out : Array (ByteArray × String) := #[]
  for (k, label) in labels do
    let some script := Wire.dataOfHex? k | throw (.labels .damaged)
    unless hex script == k && (AddressDecoder.address script network).isSome &&
        (normalizedLabel label).toOption == some label && !label.isEmpty do throw (.labels .damaged)
    out := (out.filter (·.1 != script)).push (script, label)
  return out

/-- `backup()`: script hex → note; refused while the file is unreadable. -/
def backup (s : LabelStore) : RM (Array (String × String)) := do
  if s.notice.isSome then throw (.labels .damaged)
  return s.labels.map fun (k, v) => (hex k, v)

/-- `restore(_:)`: the validated labels written (as `persist`), then adopted. -/
def restore (s : LabelStore) (writeData : WriteData) (backup : Array (String × String)) : RM LabelStore := do
  if s.notice.isSome then throw (.labels .damaged)
  let updated ← validatedBackup backup s.network
  let some p := s.path | throw (.labels .unavailable)
  unless updated.size ≤ maximumLabels do throw (.labels .full)
  let data := s.encode updated
  unless data.size ≤ maximumFileBytes do throw (.labels .full)
  RM.io (writeData data p)
  return { s with labels := updated }

end LabelStore

end WinnowApp.RecordsReal
