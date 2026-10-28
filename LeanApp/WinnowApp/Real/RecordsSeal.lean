import Std.Data.HashMap
import Winnow.Wallet
import WinnowApp.Types

/-! # Sealed store files and their keys (port of `Sources/WinnowApp/StoreAuthentication.swift`)

The records side of the app keeps a sealed JSON file per network (`people.json`; `vaults.json` went with
vaults upstream, and the app only deletes a leftover one with the wallet):

    winnow-store-mac-v1 <64 hex>⏎<the JSON payload, byte-exact>

The code is HMAC-SHA256 over `"winnow-store-mac-v1\0<store>\0<network>\0" ++ payload` under a 32-byte key
held outside the app container (the Keychain item `store-key.<store>.<network>` in the app). The key's
existence is the record that the file has been sealed once: from then on an unsealed or unverifiable file
reads as damage. The first sealed write establishes the key; if that write fails the key is discarded,
so an unsealed file still on disk is adopted next time.

Also here: the one error type every records operation fails with (`RecordsError`, a case per Swift error
type, with the Swift `kind(error)` name and `localizedDescription`), atomic file writes and bounded reads.

Not ported: iOS file protection (`completeFileProtectionUntilFirstUserAuthentication`), which belongs to
the native shell; and the constant-time comparison of the code (Swift's `isValidAuthenticationCode`),
which is a plain comparison here. -/

namespace WinnowApp.RecordsReal
open Winnow

/-! ## Errors -/

/-- `SealedStoreFile.Failure`. -/
inductive SealFailure where
  /-- The file carries no seal, and this store has a key. -/
  | unsealed
  /-- The file is sealed, and this store has no key to verify it with. -/
  | keyMissing
  | malformed
  | verificationFailed
  deriving Repr, BEq, Inhabited

def SealFailure.name : SealFailure → String
  | .unsealed => "unsealed" | .keyMissing => "keyMissing" | .malformed => "malformed"
  | .verificationFailed => "verificationFailed"

/-- `StoreKeyVaultError`. -/
inductive StoreKeyVaultError where
  | alreadyEstablished (account : String)
  | malformedKey
  | keychain (status : Int32)
  deriving Repr, BEq, Inhabited

/-- `PeopleStorageError`. -/
inductive PeopleStorageError where
  | invalidState (reason : String)
  | damaged
  | duplicate (existingName : String)
  | unknownPerson
  | tooMany
  deriving Repr, BEq, Inhabited

/-- `MultisigStorageError` (MultisigStore.swift). -/
inductive MultisigStorageError where
  | invalidState (reason : String)
  | damaged
  | duplicate
  | tooMany
  deriving Repr, BEq, Inhabited

/-- `ReceiveAddressLabelStore.StorageError`. -/
inductive LabelStorageError where
  | unavailable | damaged | invalidLabel | full
  deriving Repr, BEq, Inhabited

/-- The `AppModel.AppError` cases the records operations throw. -/
inductive AppError where
  | noWallet
  | sendReviewChanged
  | personCannotBePaid
  deriving Repr, BEq, Inhabited

/-- Every failure of a records operation. -/
inductive RecordsError where
  | seal (f : SealFailure)
  | keyVault (e : StoreKeyVaultError)
  | people (e : PeopleStorageError)
  | labels (e : LabelStorageError)
  | multisig (e : MultisigStorageError)
  | app (e : AppError)
  /-- `SenderLookupError.unavailable`. -/
  | lookup (message : String)
  /-- Another module's error: its Swift case name and its description. -/
  | named (name : String) (description : String)
  | io (e : IO.Error)
  deriving Inhabited

namespace RecordsError

/-- Swift's `kind(error)`: the enum case without its payload. -/
def name : RecordsError → String
  | .seal f => f.name
  | .keyVault (.alreadyEstablished _) => "alreadyEstablished" | .keyVault .malformedKey => "malformedKey"
  | .keyVault (.keychain _) => "keychain"
  | .people (.invalidState _) => "invalidState" | .people .damaged => "damaged"
  | .people (.duplicate _) => "duplicate" | .people .unknownPerson => "unknownPerson" | .people .tooMany => "tooMany"
  | .labels .unavailable => "unavailable" | .labels .damaged => "damaged" | .labels .invalidLabel => "invalidLabel"
  | .labels .full => "full"
  | .multisig (.invalidState _) => "invalidState" | .multisig .damaged => "damaged"
  | .multisig .duplicate => "duplicate" | .multisig .tooMany => "tooMany"
  | .app .noWallet => "noWallet"
  | .app .sendReviewChanged => "sendReviewChanged" | .app .personCannotBePaid => "personCannotBePaid"
  | .lookup _ => "unavailable"
  | .named n _ => n
  | .io _ => "ioError"

def maximumPeople : Nat := 1_000
def maximumMultisigAccounts : Nat := 100

/-- `localizedDescription`. -/
def description : RecordsError → String
  | .seal _ => "The store file could not be verified."
  | .keyVault (.alreadyEstablished a) => s!"This device already holds a protected key for the {a} file."
  | .keyVault .malformedKey => "The protected key for a store file is damaged."
  | .keyVault (.keychain s) => s!"The device could not keep a store file's protected key (keychain status {s})."
  | .people (.invalidState r) => s!"Invalid people storage: {r}"
  | .people .damaged =>
    "Winnow could not safely read your saved recipients, so they cannot be changed until the file is readable again."
  | .people (.duplicate n) => s!"That key already belongs to {n}."
  | .people .unknownPerson => "That person is no longer in your list."
  | .people .tooMany => s!"Winnow keeps at most {maximumPeople} people."
  | .labels .unavailable => "Receive address labels could not be saved on this device."
  | .labels .damaged =>
    "Receive address labels could not be read safely. The saved file was left untouched. You can still receive without a label."
  | .labels .invalidLabel => "Use a single-line label of at most 120 characters."
  | .labels .full => "This wallet has reached its limit of 10,000 receive address labels."
  | .multisig (.invalidState r) => s!"Invalid multisig storage: {r}"
  | .multisig .damaged =>
    "Winnow could not safely read its multisig accounts, so they cannot be changed until the file is readable again."
  | .multisig .duplicate => "This multisig account is already on this phone."
  | .multisig .tooMany => s!"Winnow keeps at most {maximumMultisigAccounts} multisig accounts."
  | .app .noWallet => "No wallet is open."
  | .app .sendReviewChanged => "The available coins, fee, or change changed. Review the payment again before signing."
  | .app .personCannotBePaid => "This person has no pay-to key or address yet. Ask them for their Winnow card."
  | .lookup m => m
  | .named _ d => d
  | .io e => toString e

end RecordsError

instance : ToString RecordsError := ⟨RecordsError.description⟩

/-- A records operation. -/
abbrev RM := ExceptT RecordsError IO

def RM.io {α} (x : IO α) : RM α := ExceptT.mk do
  try return .ok (← x) catch e => return .error (.io e)

def RM.lift {ε α} (f : ε → RecordsError) (r : Except ε α) : RM α :=
  match r with | .ok a => pure a | .error e => throw (f e)

/-- Runs a records operation as plain `IO`, its failure as a user error carrying the description (what
the screens show). -/
def RM.toIO {α} (x : RM α) : IO α := do
  match ← x.run with
  | .ok a => pure a
  | .error e => throw (IO.userError e.description)

/-! ## Descriptions of other modules' errors, by case name

The Lean port of WalletCore reports most failures by their Swift case name; the screens need the
sentence. These are the `errorDescription`s of the errors the records operations can meet. -/

def describe (name : String) (network : Tx.BitcoinNetwork) : String :=
  let payTo : List PersonPayToError := [.malformed, .privateKey, .singleAddressKey, .notSingleKey,
    .unsupportedDerivation, .noFixedScript]
  if let some e := payTo.find? (·.name == name) then e.description
  else if name == "wrongNetwork" then (PersonPayToError.wrongNetwork network).description
  else if name == "notACard" then PersonCardError.notACard.description
  else if name == "empty" then PersonPasteError.empty.description
  else if name == "unrecognised" then PersonPasteError.unrecognised.description
  else if name == "invalidAddress" then "That isn't a valid Bitcoin address."
  else if name == "unsupportedVersion" then "This card was made by a newer Winnow. Update the app to read it."
  else s!"The operation could not be completed ({name})."

def namedError (name : String) (network : Tx.BitcoinNetwork) : RecordsError := .named name (describe name network)

def liftNamed {α} (network : Tx.BitcoinNetwork) (r : Except String α) : RM α := RM.lift (namedError · network) r

def liftWallet {α} (network : Tx.BitcoinNetwork) (x : WM α) : RM α := do
  match ← RM.io x.run with
  | .ok a => pure a
  | .error (.wallet e) => throw (.named e.name e.description)
  | .error (.io e) => throw (.io e)
  | .error e => throw (namedError e.name network)

/-! ## Networks -/

def Network.toBitcoin : Network → Tx.BitcoinNetwork
  | .mainnet => .mainnet | .signet => .signet | .regtest => .regtest

def networkRaw (n : Tx.BitcoinNetwork) : String := Wallet.networkName n

/-! ## Store keys -/

/-- `StoreKeyVault`: where a store file's authentication key lives. -/
structure StoreKeyVault where
  /-- The key established for `account`, or none while none has been. -/
  key : String → RM (Option ByteArray)
  /-- Makes and keeps a fresh key for `account`; refuses to replace one. -/
  establishKey : String → RM ByteArray
  /-- Forgets the key for `account` (only to undo an `establishKey` whose first sealed write failed). -/
  discardKey : String → RM Unit
  /-- The item under `account` as stored, in any format; none if absent (the in-memory vault has none). -/
  rawKey : String → RM (Option ByteArray) := fun _ => pure none
  /-- Keeps `bytes` under `account` as they are, unless something is already there. -/
  keepRaw : String → ByteArray → RM Unit := fun _ _ => pure ()

def keyBytes : Nat := 32
def accountPrefix : String := "store-key."

/-- An in-memory vault (the tests' `StoreKeyVault`). -/
def StoreKeyVault.inMemory (ref : IO.Ref (Std.HashMap String ByteArray)) : StoreKeyVault where
  key a := RM.io do return (← ref.get)[a]?
  establishKey a := do
    if (← RM.io ref.get).contains a then throw (.keyVault (.alreadyEstablished a))
    let k ← RM.io (IO.getRandomBytes keyBytes.toUSize)
    RM.io (ref.modify (·.insert a k))
    return k
  discardKey a := RM.io (ref.modify (·.erase a))

/-- The vault over the Keys area's `KeyStore` (the Keychain capability on iOS): the key for account `a`
is the secret stored under `store-key.<a>`, carried as `.masterKey <64 lowercase hex>`. The Swift app
keeps the raw 32 bytes in its Keychain item instead, so a Keychain item is not shared between the two
apps; the files are. A Swift item reads as no key here (it is not text); `rawKey` sees it, and
`StoreSeal.setAsideSwiftEra` moves it and its file out of the way. -/
def StoreKeyVault.ofKeyStore (ks : Keys.KeyStore IO) : StoreKeyVault where
  key a := do
    match ← RM.io (ks.load (accountPrefix ++ a)).run with
    | .ok (.masterKey h) =>
      match ofHex? h with
      | some k => if k.size == keyBytes then pure (some k) else throw (.keyVault .malformedKey)
      | none => throw (.keyVault .malformedKey)
    | .ok (.mnemonic _) | .ok (.accountKey ..) => throw (.keyVault .malformedKey)
    | .error (.notFound _) => pure none
    | .error (.keychain s) => throw (.keyVault (.keychain s))
    | .error _ => throw (.keyVault .malformedKey)
  establishKey a := do
    let k ← RM.io (IO.getRandomBytes keyBytes.toUSize)
    match ← RM.io (ks.store (.masterKey (hex k)) (accountPrefix ++ a)).run with
    | .ok () => pure k
    | .error (.alreadyExists _) => throw (.keyVault (.alreadyEstablished a))
    | .error (.keychain s) => throw (.keyVault (.keychain s))
    | .error _ => throw (.keyVault .malformedKey)
  discardKey a := do
    match ← RM.io (ks.delete (accountPrefix ++ a)).run with
    | .ok () => pure ()
    | .error (.notFound _) => pure ()
    | .error (.keychain s) => throw (.keyVault (.keychain s))
    | .error _ => throw (.keyVault .malformedKey)
  rawKey a := do
    match ← RM.io (ks.loadBytes (accountPrefix ++ a)).run with
    | .ok b => pure b
    | .error (.keychain s) => throw (.keyVault (.keychain s))
    | .error _ => throw (.keyVault .malformedKey)
  keepRaw a bytes := do
    match ← RM.io (ks.storeBytes bytes (accountPrefix ++ a)).run with
    | .ok () | .error (.alreadyExists _) => pure ()
    | .error (.keychain s) => throw (.keyVault (.keychain s))
    | .error _ => throw (.keyVault .malformedKey)

/-! ## The sealed file -/

namespace SealedStoreFile

def header : String := "winnow-store-mac-v1"
def «prefix» : ByteArray := (header ++ " ").toUTF8

def domain (store : String) (network : Tx.BitcoinNetwork) : ByteArray :=
  (header ++ "\x00" ++ store ++ "\x00" ++ networkRaw network ++ "\x00").toUTF8

def code (payload : ByteArray) (store : String) (network : Tx.BitcoinNetwork) (key : ByteArray) : ByteArray :=
  hmacSha256 key (domain store network ++ payload)

def sealed (payload : ByteArray) (store : String) (network : Tx.BitcoinNetwork) (key : ByteArray) : ByteArray :=
  «prefix» ++ (hex (code payload store network key) ++ "\n").toUTF8 ++ payload

def isSealed (data : ByteArray) : Bool :=
  data.size ≥ «prefix».size && data.extract 0 «prefix».size == «prefix»

def firstNewline (data : ByteArray) : Option Nat := Id.run do
  for i in [0:data.size] do
    if data[i]! == 0x0A then return some i
  return none

/-- `HMAC.isValidAuthenticationCode`'s comparison: every byte is visited whatever differs, so the time does
not depend on where a forged code first goes wrong. -/
def constantTimeEqual (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  let mut diff : UInt8 := 0
  for i in [0:a.size] do
    diff := diff ||| (a[i]! ^^^ b[i]!)
  return diff == 0

/-- The payload of a sealed file, once its code verifies. The code's text is read as WalletCore's
`Data(hex:)` reads it (whitespace trimmed, a sign accepted per byte). -/
def «open» (data : ByteArray) (store : String) (network : Tx.BitcoinNetwork) (key : ByteArray) :
    Except SealFailure ByteArray := do
  unless isSealed data do throw .unsealed
  let some nl := firstNewline data | throw .malformed
  let text := Keys.Unicode.decodeUTF8Lossy (data.extract «prefix».size nl)
  let some c := Wire.dataOfHex? text | throw .malformed
  unless c.size == 32 do throw .malformed
  let payload := data.extract (nl + 1) data.size
  unless constantTimeEqual (code payload store network key) c do throw .verificationFailed
  return payload

end SealedStoreFile

/-- `StoreSeal`: one store file's seal. -/
structure StoreSeal where
  store : String
  keys : StoreKeyVault

namespace StoreSeal

def account (s : StoreSeal) (network : Tx.BitcoinNetwork) : String := s.store ++ "." ++ networkRaw network

/-- The payload of `data`, and whether it predates sealing (no key yet, unsealed: adopted as it is). -/
def read (s : StoreSeal) (data : ByteArray) (network : Tx.BitcoinNetwork) : RM (ByteArray × Bool) := do
  match ← s.keys.key (s.account network) with
  | none =>
    if SealedStoreFile.isSealed data then throw (.seal .keyMissing)
    return (data, true)
  | some key =>
    let payload ← RM.lift RecordsError.seal (SealedStoreFile.open data s.store network key)
    return (payload, false)

/-- Writes `payload` sealed; the first write establishes the key, and discards it again if it fails. -/
def write (s : StoreSeal) (payload : ByteArray) (network : Tx.BitcoinNetwork) (path : System.FilePath)
    (writeData : ByteArray → System.FilePath → IO Unit) : RM Unit := do
  let account := s.account network
  let existing ← s.keys.key account
  let key ← match existing with | some k => pure k | none => s.keys.establishKey account
  try
    RM.io (writeData (SealedStoreFile.sealed payload s.store network key) path)
  catch e =>
    if existing.isNone then discard <| RM.io (s.keys.discardKey account).run
    throw e

end StoreSeal

/-! ## Files -/

/-- `Data.write(to:options: .atomic)`: a temporary file beside the target, then a rename over it. -/
def writeAtomically (data : ByteArray) (path : System.FilePath) : IO Unit := do
  let name := path.fileName.getD "store.json"
  let tmp := path.withFileName s!".{name}.{hex (← IO.getRandomBytes 6)}.tmp"
  try
    IO.FS.writeBinFile tmp data
    IO.FS.rename tmp path
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw e

/-- How a store writes its file (injectable, so a test can make a write fail). -/
abbrev WriteData := ByteArray → System.FilePath → IO Unit

/-- Measures before reading, so a planted file is refused rather than held. -/
def boundedRead (path : System.FilePath) (maximum : Nat) (tooLarge : RecordsError) : RM ByteArray := do
  let size ← RM.io do return (← path.metadata).byteSize
  if size.toNat > maximum then throw tooLarge
  let data ← RM.io (IO.FS.readBinFile path)
  if data.size > maximum then throw tooLarge
  return data

def fileExists (path : System.FilePath) : IO Bool := path.pathExists

/-- `UUID().uuidString`: a random (version 4) UUID, uppercase. -/
def uuidString : IO String := do
  let b ← IO.getRandomBytes 16
  let b := (b.set! 6 ((b[6]! &&& 0x0F) ||| 0x40)).set! 8 ((b[8]! &&& 0x3F) ||| 0x80)
  let h := (hex b).toUpper
  let part (i n : Nat) := ((h.drop i).take n).toString
  return s!"{part 0 8}-{part 8 4}-{part 12 4}-{part 16 4}-{part 20 12}"

/-! ## Stores the Swift app left -/

def swiftEraPrefix : String := "swift-era."

/-- `<stem>.swift-era.<ext>` beside `path`, or `<stem>.swift-era-<n>.<ext>` if that is taken. -/
def swiftEraPath (path : System.FilePath) : IO System.FilePath := do
  let stem := path.fileStem.getD "store"
  let ext := path.extension.map ("." ++ ·) |>.getD ""
  for n in [1:1000] do
    let suffix := if n == 1 then "" else s!"-{n}"
    let candidate := path.withFileName s!"{stem}.swift-era{suffix}{ext}"
    unless ← fileExists candidate do return candidate
  throw (IO.userError s!"no free name beside {path}")

/-- Sets aside a store the Swift app left, so this app starts it empty instead of locking it. The Swift
app sealed its file under a raw 32-byte Keychain key, which this app reads as no key, so the file would
read as damage and refuse every change. The key moves to `swift-era.<account>` and the file to
`<stem>.swift-era.json` beside it; neither is read again or deleted. A key this app wrote is text, never
32 bytes, so its stores are left alone and a damaged file under one still reads as damage. Each step can
be repeated, so a set-aside interrupted between the key and the file finishes at the next open. Whether
anything was set aside. -/
def StoreSeal.setAsideSwiftEra (s : StoreSeal) (network : Tx.BitcoinNetwork) (path : System.FilePath) : RM Bool := do
  let account := s.account network
  let aside := swiftEraPrefix ++ account
  match ← s.keys.rawKey account with
  | some raw =>
    unless raw.size == keyBytes do return false
    match ← s.keys.rawKey aside with
    | none => s.keys.keepRaw aside raw
    | some k => unless k == raw do throw (.keyVault (.alreadyEstablished aside))
    s.keys.discardKey account
  | none =>
    unless ← RM.io (fileExists path) do return false
    if (← s.keys.rawKey aside).isNone then return false
  if ← RM.io (fileExists path) then RM.io (IO.FS.rename path (← swiftEraPath path))
  return true

end WinnowApp.RecordsReal
