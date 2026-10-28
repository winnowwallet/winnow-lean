import Std.Data.HashSet
import Std.Sync.Mutex
import Std.Time
import WinnowApp.Real.RecordsStores
import Winnow.Wallet.SignerRecord
import Winnow.Ledger.Multisig

/-! # The signers a phone knows (port of `Sources/WinnowApp/SignerStore.swift`, upstream d2ca878)

The list under Settings → Signers, from which the multisig builder takes its members and the Join
screen its member share: a Ledger the phone paired, or keys other people sent (`SignerRecord`). One
sealed JSON file per network, `signers.json`, read under the same seal as the other stores (store name
`signers`) and carried in every backup. Public keys only, so the file is not a wallet's: it survives
deleting one (it is not among the per-wallet files the wallet deletion removes), like `people.json`.
Damage is reported, the file left untouched and every mutation refused until it reads again; the
wallet itself carries on.

As `MultisigStore.lean` does, the actor becomes an immutable value: every mutation returns the next
store (or fails and the caller keeps the old one). `SignerHost` keeps the current value behind one mutex.

Errors: `SignerStorageError` travels as `RecordsError.named` with Swift's case name and
`errorDescription`, so the records' error type is unchanged. -/

namespace WinnowApp.RecordsReal
open Winnow SwiftJSON
open Tx (BitcoinNetwork)

/-- `SignerStorageError`. -/
inductive SignerStorageError where
  | invalidState (reason : String)
  | damaged
  | duplicate (existingName : String)
  | unknownSigner
  | tooMany
  deriving Repr, BEq, Inhabited

namespace SignerStorageError

def name : SignerStorageError → String
  | .invalidState _ => "invalidState" | .damaged => "damaged" | .duplicate _ => "duplicate"
  | .unknownSigner => "unknownSigner" | .tooMany => "tooMany"

def description : SignerStorageError → String
  | .invalidState r => s!"Invalid signer storage: {r}"
  | .damaged => "Winnow could not safely read its signers, so they cannot be changed until the file is readable again."
  | .duplicate n => s!"That key is already saved as {n}."
  | .unknownSigner => "That signer is no longer on this phone."
  | .tooMany => s!"Winnow keeps at most {SignerRecord.maximumSigners} signers."

def toRecords (e : SignerStorageError) : RecordsError := .named e.name e.description

end SignerStorageError

/-- `SignerStore`. -/
structure SignerStore where
  records : Array SignerRecord := #[]
  path : Option System.FilePath := none
  network : BitcoinNetwork := .signet
  isDamaged : Bool := false
  deriving Inhabited

namespace SignerStore

def maximumFileBytes : Nat := 1_024 * 1_024
def storeName : String := "signers"
def fileName : String := "signers.json"

def damagedStorageMessage : String :=
  "Winnow found its signer list but could not safely read it. The file and protected keys were left untouched. Retry; if this continues, pair the Ledger and save the keys again, or ask for help before changing anything."

def unverifiedStorageMessage : String :=
  "Winnow found a signer list it could not verify: the file was not written by Winnow on this device, or its protected key is gone. The file and protected keys were left untouched. Pair the Ledger and save the keys again, or ask for help before changing anything."

def fail {α} (e : SignerStorageError) : RM α := throw e.toRecords
def invalid {α} (reason : String) : RM α := fail (.invalidState reason)

def storeSeal (keys : StoreKeyVault) : StoreSeal := { store := storeName, keys }

/-- A `MultisigAccount` failure (a key that does not parse) as the screens describe it. -/
def accountFailure : MultisigFailure → RecordsError
  | .account e => .named e.name e.description
  | .named n => .named n n

/-- `identities(of:network:)`: the compressed account public keys behind key expressions, which must all
parse as signers on this network. -/
def identities (keys : Array String) (network : BitcoinNetwork) : RM (Array ByteArray) :=
  keys.mapM fun key => do
    let single ← RM.lift accountFailure (MultisigAccount.signerKey key network)
    match single.base with
    | .extended xpub _ => pure xpub.publicKey
    | _ => invalid "a signer key is not an extended key"

/-- `usableName`: a short single-line name, as the other stores take one. -/
def usableName (name : String) : RM String := do
  let some n := DisplayName.normalized name | invalid "a signer needs a short, single-line name"
  return n

/-- `validateKind`: a Ledger's record carries its one key at the Ledger's path under its own
fingerprint; saved keys carry no device fingerprint. -/
def validateKind (r : SignerRecord) (network : BitcoinNetwork) : RM Unit := do
  match r.kind with
  | .ledger =>
    let key ← RM.lift accountFailure (MultisigAccount.signerKey r.keys[0]! network)
    let ok := r.keys.size == 1 && (match r.masterFingerprint, key.origin with
      | some fp, some o => o.fingerprint == fp && o.path == Ledger.Multisig.keyPath network
      | _, _ => false)
    unless ok do invalid "a Ledger's record does not carry its own key"
  | .keys =>
    unless r.masterFingerprint.isNone do invalid "saved keys carry no device fingerprint"

/-- `validate(_:network:)`: unique ids and names in shape, every key a signer on this network and held
by one record, each kind as it must be. -/
def validate (records : Array SignerRecord) (network : BitcoinNetwork) : RM Unit := do
  unless records.size ≤ SignerRecord.maximumSigners do invalid "too many signers"
  let mut ids : Std.HashSet String := {}
  let mut held : Std.HashSet ByteArray := {}
  for r in records do
    if r.id.isEmpty || ids.contains r.id then invalid "duplicate signer identifier"
    ids := ids.insert r.id
    unless DisplayName.normalized r.name == some r.name && !r.name.isEmpty do invalid "a signer has no usable name"
    unless 1 ≤ r.keys.size && r.keys.size ≤ SignerRecord.maximumKeysPerSigner do
      invalid "a signer has no keys, or too many"
    for identity in ← identities r.keys network do
      if held.contains identity then invalid "a key is held by two signers"
      held := held.insert identity
    validateKind r network

def encode (records : Array SignerRecord) : ByteArray :=
  (write (.arr (records.map SignerRecord.toJV))).toUTF8

def decode (payload : ByteArray) : RM (Array SignerRecord) := do
  let some text := String.fromUTF8? payload | throw (.named "dataCorrupted" "The signer file is not valid JSON.")
  RM.lift (fun e => .named e "The signer file could not be decoded.") (decodeText text (asArray SignerRecord.ofJV))

/-- `validateBackup(_:network:)`: a backup's list as the store would keep it, within the file's size. -/
def validateBackup (backup : Array SignerRecord) (network : BitcoinNetwork) : RM Unit := do
  validate backup network
  unless (encode backup).size ≤ maximumFileBytes do invalid "invalid cloud signer list"

/-- `mutate`: persist the candidate records, then adopt them (the old store stays when the write fails). -/
def mutate (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (candidate : Array SignerRecord) :
    RM SignerStore := do
  if let some p := s.path then (storeSeal keys).write (encode candidate) s.network p writeData
  return { s with records := candidate }

/-- `configure(storageURL:network:)`: loads an existing file. An unsealed one was put there by something
else (no Winnow wrote this file before sealing existed), so it is refused. -/
def configure (keys : StoreKeyVault) (path : Option System.FilePath) (network : BitcoinNetwork) :
    IO (SignerStore × OpenResult) := do
  let empty : SignerStore := { path, network }
  let some p := path | return (empty, .missing)
  -- a store the Swift app left is set aside and starts empty; if that fails, it reads as damage below
  discard <| ((storeSeal keys).setAsideSwiftEra network p).run
  unless ← fileExists p do return (empty, .missing)
  let attempt : RM (Array SignerRecord) := do
    let data ← boundedRead p maximumFileBytes (SignerStorageError.invalidState "signer file too large").toRecords
    let (payload, predates) ← (storeSeal keys).read data network
    if predates then throw (.seal .unsealed)
    let decoded ← decode payload
    validate decoded network
    return decoded
  match ← attempt.run with
  | .ok records => return ({ empty with records }, .loaded)
  | .error e =>
    return ({ empty with isDamaged := true },
            .damaged (if isSealFailure e then unverifiedStorageMessage else damagedStorageMessage))

def requireReadable (s : SignerStore) : RM Unit := do
  if s.isDamaged then fail .damaged

def record? (s : SignerStore) (id : String) : Option SignerRecord := s.records.find? (·.id == id)

/-- `append`: refuses past the ceiling and any key another record already holds. -/
def append (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (r : SignerRecord) : RM SignerStore := do
  unless s.records.size < SignerRecord.maximumSigners do fail .tooMany
  let identities ← identities r.keys s.network
  for holder in s.records do
    let theirs ← SignerStore.identities holder.keys s.network
    if theirs.any identities.contains then fail (.duplicate holder.name)
  s.mutate keys writeData (s.records.push r)

/-- `addLedger(name:key:fingerprint:)`: files a paired Ledger; pairing the same Ledger again renames the
record it has rather than adding a copy. -/
def addLedger (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (name key : String)
    (fingerprint : UInt32) (id : String) (addedAt : Float) : RM (SignerStore × SignerRecord) := do
  s.requireReadable
  let name ← usableName name
  if let some i := s.records.findIdx? (fun r => r.isLedger && r.masterFingerprint == some fingerprint && r.keys == #[key]) then
    let next ← s.mutate keys writeData (s.records.modify i fun r => { r with name })
    return (next, next.records[i]!)
  let r : SignerRecord := { id, kind := .ledger, name, keys := #[key], masterFingerprint := some fingerprint, addedAt }
  -- the record must be what `validate` takes back from disk
  validateKind r s.network
  return (← s.append keys writeData r, r)

/-- `addKeys(name:keys:)`: files keys someone sent as one signer. -/
def addKeys (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (name : String) (signerKeys : Array String)
    (id : String) (addedAt : Float) : RM (SignerStore × SignerRecord) := do
  s.requireReadable
  let r : SignerRecord := { id, kind := .keys, name := ← usableName name, keys := signerKeys, addedAt }
  unless 1 ≤ signerKeys.size && signerKeys.size ≤ SignerRecord.maximumKeysPerSigner do
    invalid "a signer has no keys, or too many"
  return (← s.append keys writeData r, r)

def rename (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (id name : String) : RM SignerStore := do
  s.requireReadable
  let some i := s.records.findIdx? (·.id == id) | fail .unknownSigner
  let name ← usableName name
  s.mutate keys writeData (s.records.modify i fun r => { r with name })

def remove (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (id : String) : RM SignerStore := do
  s.requireReadable
  unless s.records.any (·.id == id) do fail .unknownSigner
  s.mutate keys writeData (s.records.filter (·.id != id))

/-- `backup()`: the records for a backup. -/
def backup (s : SignerStore) : RM (Array SignerRecord) := do
  s.requireReadable
  return s.records

/-- `planRestore(_:)`: keeps the signers already on this phone and adds the restored ones it does not
have, by id or by key; the rest are dropped at the ceiling. -/
def planRestore (s : SignerStore) (incoming : Array SignerRecord) : RM (Array SignerRecord) := do
  s.requireReadable
  validateBackup incoming s.network
  let mut merged := s.records
  let mut held : Std.HashSet ByteArray := {}
  for r in merged do
    for i in ← identities r.keys s.network do held := held.insert i
  for r in incoming do
    unless merged.size < SignerRecord.maximumSigners do continue
    let ids ← identities r.keys s.network
    if merged.any (·.id == r.id) || ids.any held.contains then continue
    merged := merged.push r
    for i in ids do held := held.insert i
  validateBackup merged s.network
  return merged

def restore (s : SignerStore) (keys : StoreKeyVault) (writeData : WriteData) (backup : Array SignerRecord) :
    RM SignerStore := do
  s.requireReadable
  validateBackup backup s.network
  s.mutate keys writeData backup

end SignerStore

/-! ## The current store -/

/-- The signer store of the open network directory, behind one mutex (the Swift actor's isolation). -/
structure SignerHost where
  keys : StoreKeyVault
  writeData : WriteData := writeAtomically
  state : Std.Mutex SignerStore
  /-- `signerStorageNotice`: set when `signers.json` could not be read. -/
  notice : IO.Ref (Option String)

namespace SignerHost

def new (keys : StoreKeyVault) (writeData : WriteData := writeAtomically) : IO SignerHost := do
  return { keys, writeData, state := ← Std.Mutex.new {}, notice := ← IO.mkRef none }

def read (h : SignerHost) : IO SignerStore := h.state.atomically get

def modify {α} (h : SignerHost) (f : SignerStore → RM (SignerStore × α)) : RM α :=
  h.state.atomically do
    let s ← get
    let (s', a) ← (f s : RM _)
    set s'
    return a

/-- `configureSigners()`: reads `signers.json` of `dir` (none: unreachable storage, nothing persisted). -/
def configure (h : SignerHost) (network : BitcoinNetwork) (dir : Option System.FilePath) : IO Unit := do
  let (store, result) ← SignerStore.configure h.keys (dir.map (· / SignerStore.fileName)) network
  h.state.atomically (set store)
  h.notice.set (match result with | .damaged m => some m | _ => none)

def all (h : SignerHost) : IO (Array SignerRecord) := return (← h.read).records

end SignerHost

end WinnowApp.RecordsReal
