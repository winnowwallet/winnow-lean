import Winnow.Wallet.Wallet
import Winnow.Wallet.Characters

/-! # People and cards (port of `Sources/WalletCore/Wallet/People.swift`)

Pay-to keys (`PersonPayTo`), the person card (`PersonCard`) in Winnow's one card shape (sorted keys,
unescaped slashes, a `winnow` kind field, a 64 KiB ceiling), `DisplayName` and the Add-person paste
parser. Upstream (1cf93fb) removed signer keys, cosigner fingerprints, the shared-savings and approval
cards and the savings payment labels with vaults; a card or record written with a `signerKey` still
decodes, the field ignored. A person may be paid by a silent payment code (`.silentPayment`). -/

namespace Winnow
open SwiftJSON Keys
open Tx (BitcoinNetwork)

/-! ## Pay-to -/

inductive PersonPayTo where
  | descriptor (canonical : String)
  | address (address : String)
  /-- A BIP352 code, canonical lower case: reusable like a descriptor, but the address is derived from the
  sender's inputs, so there is no script to watch for or match against. -/
  | silentPayment (code : String)
  deriving Inhabited, BEq

inductive PersonPayToError where
  | malformed | privateKey | singleAddressKey | notSingleKey
  | wrongNetwork (expected : BitcoinNetwork)
  | unsupportedDerivation
  /-- a silent payment code has no script of its own -/
  | noFixedScript
  deriving Inhabited, BEq

namespace PersonPayToError
def name : PersonPayToError → String
  | .malformed => "malformed" | .privateKey => "privateKey" | .singleAddressKey => "singleAddressKey"
  | .notSingleKey => "notSingleKey" | .wrongNetwork _ => "wrongNetwork" | .unsupportedDerivation => "unsupportedDerivation"
  | .noFixedScript => "noFixedScript"

def description : PersonPayToError → String
  | .noFixedScript => "A silent payment code has no fixed address; its payments are derived when they are sent."
  | .malformed => "That isn't a valid pay-to key. Paste the person's Winnow card or their public account key."
  | .privateKey => "That is a private key. For safety, paste only the public account key—never a seed phrase or private key."
  | .singleAddressKey => "This key gives one address only — paste the address itself instead."
  | .notSingleKey =>
    "Winnow pays a person from a single-key descriptor such as tr([…]xpub…/<0;1>/*)."
  | .wrongNetwork n => s!"That key is for a different Bitcoin network. This wallet is on {Wallet.networkName n}."
  | .unsupportedDerivation =>
    "This key derives addresses in a way Winnow cannot follow. Paste the account key ending in /<0;1>/* or /0/*."
end PersonPayToError

/-- Failures of the people module: a domain error, or another module's by case name. -/
abbrev PM := Except String

namespace PersonPayTo

/-- The receive/change shape every Winnow account key carries. -/
def receiveChangeDerivation : Array Descriptor.Element := #[.multipath #[0, 1], .wildcard false]

/-- The one other derivation a pay-to key may carry: receive chain only. -/
def receiveOnlyDerivation : Array Descriptor.Element := #[.step 0, .wildcard false]

/-- Validates a pay-to descriptor and returns it in canonical form. -/
def ofDescriptor (text : String) (network : BitcoinNetwork) : Except PersonPayToError PersonPayTo := do
  let trimmed := Unicode.trimWhitespace text
  let some d := (Descriptor.parse trimmed).toOption | throw .malformed
  let .tr key := d.expression | throw .notSingleKey
  match key.base with
  | .privateKey .. => throw .privateKey
  | .publicKey _ => throw .singleAddressKey
  | .extended hd keyNetwork =>
    if hd.isPrivate then throw .privateKey
    unless keyNetwork == Wallet.hdNetwork network do throw (.wrongNetwork network)
  let els := key.derivation.elements
  unless els == receiveChangeDerivation || els == receiveOnlyDerivation do
    throw (if key.derivation.isRanged then .unsupportedDerivation else .singleAddressKey)
  if (d.derived 0 network).toOption.isNone then throw .malformed
  return .descriptor d.serialized

/-- Validates a plain address (with `AddressError`'s own case). -/
def ofAddress (text : String) (network : BitcoinNetwork) : Except String PersonPayTo := do
  let trimmed := Unicode.trimWhitespace text
  discard <| (AddressDecoder.scriptPubKey trimmed network).mapError (·.name)
  return .address trimmed

/-- Validates a silent payment code on `network` and returns it in canonical (lower-case) form. -/
def ofSilentPayment (text : String) (network : BitcoinNetwork) : Except SilentPaymentAddressError PersonPayTo := do
  let code ← SilentPaymentAddress.decode (Unicode.trimWhitespace text) (some (SilentPayment.hrp (network == .mainnet)))
  return .silentPayment (← code.encoded.mapError .encoding)

/-- Whether the payment index moves with each payment (a code is reusable by derivation, not counting). -/
def derivesFreshAddresses : PersonPayTo → Bool | .descriptor _ => true | _ => false
def isSilentPayment : PersonPayTo → Bool | .silentPayment _ => true | _ => false
def text : PersonPayTo → String | .descriptor v | .address v | .silentPayment v => v

def derivedAt (text : String) (index : UInt32) (network : BitcoinNetwork) : PM Descriptor.DerivedOutput := do
  let d ← (Descriptor.parse text).mapError (·.name)
  let outs ← (d.derived index network).mapError (·.name)
  let some o := outs[0]? | throw "indexOutOfRange"
  return o

def addressAt (p : PersonPayTo) (index : UInt32) (network : BitcoinNetwork) : PM String :=
  match p with
  | .address a | .silentPayment a => pure a
  | .descriptor t => return (← derivedAt t index network).address

def scriptPubKeyAt (p : PersonPayTo) (index : UInt32) (network : BitcoinNetwork) : PM ByteArray :=
  match p with
  | .address a => (AddressDecoder.scriptPubKey a network).mapError (·.name)
  | .descriptor t => return (← derivedAt t index network).scriptPubKey
  | .silentPayment _ => throw PersonPayToError.noFixedScript.name

def scripts (p : PersonPayTo) (count : UInt32) (network : BitcoinNetwork) : PM (Array ByteArray) :=
  match p with
  | .address _ => return #[← p.scriptPubKeyAt 0 network]
  | .descriptor _ => (Array.range count.toNat).mapM fun i => p.scriptPubKeyAt i.toUInt32 network
  -- a code's outputs are labelled from the send that made them
  | .silentPayment _ => return #[]

/-- What makes two pay-to keys one person's: the script at index 0, or a code's two keys (66 bytes, longer
than any script Winnow pays, so the kinds cannot collide). -/
def identity (p : PersonPayTo) (network : BitcoinNetwork) : PM ByteArray :=
  match p with
  | .silentPayment code => do
    let a ← (SilentPaymentAddress.decode code).mapError (·.name)
    return a.scanKey ++ a.spendKey
  | _ => p.scriptPubKeyAt 0 network

def toJV : PersonPayTo → JV
  | .descriptor v => .obj #[("kind", .str "descriptor"), ("value", .str v)]
  | .address v => .obj #[("kind", .str "address"), ("value", .str v)]
  | .silentPayment v => .obj #[("kind", .str "silentPayment"), ("value", .str v)]

def ofJV (v : JV) : D PersonPayTo := do
  let kvs ← asObject v
  let kind ← key kvs "kind" asString
  let value ← key kvs "value" asString
  match kind with
  | "descriptor" => pure (.descriptor value)
  | "address" => pure (.address value)
  | "silentPayment" => pure (.silentPayment value)
  | _ => dataCorrupted

end PersonPayTo

/-! ## Display names -/

namespace DisplayName

def maximumLength : Nat := 120

def cfRanges : List (Nat × Nat) :=
  [(0xAD, 0xAD), (0x600, 0x605), (0x61C, 0x61C), (0x6DD, 0x6DD), (0x70F, 0x70F), (0x890, 0x891), (0x8E2, 0x8E2),
   (0x180E, 0x180E), (0x200B, 0x200F), (0x202A, 0x202E), (0x2060, 0x2064), (0x2066, 0x206F), (0xFEFF, 0xFEFF),
   (0xFFF9, 0xFFFB), (0x110BD, 0x110BD), (0x110CD, 0x110CD), (0x13430, 0x1343F), (0x1BCA0, 0x1BCA3),
   (0x1D173, 0x1D17A), (0xE0001, 0xE0001), (0xE0020, 0xE007F)]

/-- `CharacterSet.controlCharacters` (Cc, Cf) or `.newlines`. -/
def isControlOrNewline (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7F ≤ n && n ≤ 0x9F) || n == 0x85 || n == 0x2028 || n == 0x2029 ||
    cfRanges.any fun (a, b) => a ≤ n && n ≤ b

/-- Trimmed, at most 120 `Character`s, single-line, free of control characters. -/
def normalized (text : String) : Option String :=
  let name := Unicode.trimWhitespace text
  if name.isEmpty || Characters.count name > maximumLength || name.toList.any isControlOrNewline then none else some name

end DisplayName

/-! ## Cards -/

inductive PersonCardError where
  | notACard
  | unsupportedVersion (version : Int)
  | wrongNetwork (card : String) (wallet : BitcoinNetwork)
  deriving Inhabited

def PersonCardError.name : PersonCardError → String
  | .notACard => "notACard" | .unsupportedVersion _ => "unsupportedVersion" | .wrongNetwork .. => "wrongNetwork"

def PersonCardError.description : PersonCardError → String
  | .notACard => "That isn't a Winnow card."
  | .unsupportedVersion v => s!"This card was made by a newer Winnow (card version {v}). Update the app to read it."
  | .wrongNetwork card wallet => s!"This card is for {card}; this wallet is on {Wallet.networkName wallet}."

/-- What a paste on the Add-person screen can fail with (thrown by case name: `empty`, `unrecognised`). -/
inductive PersonPasteError where
  | empty | unrecognised
  deriving Inhabited, BEq

def PersonPasteError.name : PersonPasteError → String | .empty => "empty" | .unrecognised => "unrecognised"

def PersonPasteError.description : PersonPasteError → String
  | .empty => "Paste the person's Winnow card, their public account key, or a Bitcoin address."
  | .unrecognised => "That doesn't look like a Winnow card, a public account key or a Bitcoin address."

namespace WinnowCardCoding

def maximumBytes : Nat := 64 * 1024

def serialize (v : JV) : String := writeUnescaped v

/-- The envelope's `winnow` must name `kind`; any other decoding failure is `notACard`. -/
def decode {α} (text : String) (kind : String) (f : JV → D α) : Except PersonCardError α := do
  let trimmed := Unicode.trimWhitespace text
  if trimmed.toUTF8.size > maximumBytes then throw .notACard
  let envelope : D (Option String) := decodeText trimmed fun v => do
    let kvs ← asObject v
    keyIfPresent kvs "winnow" asString
  match envelope with
  | .ok (some k) => if k != kind then throw .notACard
  | _ => throw .notACard
  match decodeText trimmed f with
  | .ok a => pure a
  | .error _ => throw .notACard

end WinnowCardCoding

def cardVersionOK (v : Int) : Bool := 1 ≤ v && v ≤ 1

structure PersonCard where
  winnow : String := "person-card"
  version : Int := 1
  network : String
  name : String
  /-- Canonical pay-to descriptor, or a plain address. -/
  payTo : Option String := none
  deriving Inhabited, BEq

namespace PersonCard
def kind : String := "person-card"

def make (network : BitcoinNetwork) (name : String) (payTo : Option String) : PersonCard :=
  { network := Wallet.networkName network, name, payTo }

def toJV (c : PersonCard) : JV :=
  obj [("winnow", some (.str c.winnow)), ("version", some (ofInt c.version)), ("network", some (.str c.network)),
    ("name", some (.str c.name)), ("payTo", c.payTo.map .str)]

def ofJV (v : JV) : D PersonCard := do
  let kvs ← asObject v
  return { winnow := ← key kvs "winnow" asString, version := ← key kvs "version" asInt, network := ← key kvs "network" asString,
           name := ← key kvs "name" asString, payTo := ← keyIfPresent kvs "payTo" asString }

def serialized (c : PersonCard) : String := WinnowCardCoding.serialize c.toJV

def decode (text : String) : Except PersonCardError PersonCard := do
  let c ← WinnowCardCoding.decode text kind ofJV
  unless cardVersionOK c.version do throw (.unsupportedVersion c.version)
  return c
end PersonCard

/-! ## Paste -/

inductive PersonImport.Source where
  | card | keyExpression | descriptor | address
  deriving Inhabited, BEq

def PersonImport.Source.name : PersonImport.Source → String
  | .card => "card" | .keyExpression => "keyExpression" | .descriptor => "descriptor" | .address => "address"

structure PersonImport where
  name : Option String
  payTo : Option PersonPayTo
  source : PersonImport.Source
  deriving Inhabited, BEq

namespace PersonPaste

def asciiLower (s : String) : String := s.map Char.toLower

/-- An address-shaped paste keeps its address error (a wrong network, say). -/
def addressError (text : String) (network : BitcoinNetwork) : Option String :=
  let lowered := asciiLower text
  let looks := ["bc1", "tb1", "1", "3", "m", "n", "2"].any (lowered.startsWith ·) && !((lowered.splitOn "pub").length > 1)
  if !looks then none
  else match AddressDecoder.scriptPubKey text network with
    | .ok _ => none
    | .error e => some e.name

def parseCard (text : String) (network : BitcoinNetwork) : PM PersonImport := do
  let card ← (PersonCard.decode text).mapError (·.name)
  unless card.network == Wallet.networkName network do throw "wrongNetwork"
  let mut payTo : Option PersonPayTo := none
  if let some raw := card.payTo.map Unicode.trimWhitespace then
    if !raw.isEmpty then
      payTo ← if raw.startsWith "tr(" then (PersonPayTo.ofDescriptor raw network).mapError (·.name) |>.map some
        else if SilentPaymentAddress.looksLikeCode raw then (PersonPayTo.ofSilentPayment raw network).mapError (·.name) |>.map some
        else (PersonPayTo.ofAddress raw network).map some
  return { name := DisplayName.normalized card.name, payTo, source := .card }

/-- A bare key expression: `[fp/path]tpub…/<0;1>/*` as Winnow exports it, or an account key without a
suffix, which gets the receive/change shape (or, for a key with no origin, the receive chain) added. A
private key or a key for another network is refused by name; anything else is unrecognised. -/
def parseKeyExpression (text : String) (network : BitcoinNetwork) : PM PersonImport := do
  for candidate in [text, text ++ "/<0;1>/*", text ++ "/0/*"] do
    match PersonPayTo.ofDescriptor s!"tr({candidate})" network with
    | .ok payTo => return { name := none, payTo := some payTo, source := .keyExpression }
    | .error .privateKey => throw "privateKey"
    | .error (.wrongNetwork _) => throw "wrongNetwork"
    | .error _ => continue
  throw "unrecognised"

/-- Whatever was pasted on the Add-person screen, validated into a person's fields. -/
def parse (text : String) (network : BitcoinNetwork) : PM PersonImport := do
  let trimmed := Unicode.trimWhitespace text
  if trimmed.isEmpty then throw "empty"
  if trimmed.startsWith "{" then return ← parseCard trimmed network
  if trimmed.startsWith "tr(" || trimmed.startsWith "rawtr(" then
    let payTo ← (PersonPayTo.ofDescriptor trimmed network).mapError (·.name)
    return { name := none, payTo := some payTo, source := .descriptor }
  -- a code: a wrong network is worth saying; anything else that merely looks like one is unrecognised
  if SilentPaymentAddress.looksLikeCode trimmed then
    match PersonPayTo.ofSilentPayment trimmed network with
    | .ok payTo => return { name := none, payTo := some payTo, source := .address }
    | .error e@(.wrongHRP ..) => throw e.name
    | .error _ => throw "unrecognised"
  if let .ok payTo := PersonPayTo.ofAddress trimmed network then
    return { name := none, payTo := some payTo, source := .address }
  if let some e := addressError trimmed network then throw e
  parseKeyExpression trimmed network

end PersonPaste

end Winnow
