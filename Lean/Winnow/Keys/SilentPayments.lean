import Winnow.Crypto
import Winnow.Keys.Secp256k1
import Winnow.Keys.Taproot

/-! # BIP352 silent payments, send side (`SilentPayments/SilentPaymentAddress.swift`, `Sending.swift`)

A recipient publishes one reusable code (`sp1…`, or `tsp1…` on test networks); every payment to it lands
on a fresh Taproot output that only the two parties can tie to the code. Winnow sends to codes and does
not receive at one. Here: the address codec, which inputs count, the sum of their keys, the input hash
over the smallest outpoint, the shared secret with the scan key, and the output keys tweaked from the
spend key. The curve work is `Secp256k1` (the proven `Secp`); errors and their order are Swift's.

The code (`SilentPaymentAddress`) lives in `Winnow`: wallet records name the code a history output was
paid to and are validated with `parse`. Differences: Swift's `SegwitAddress.convertBits` throws its own
`Bech32Error` out of the address initializer; here it is the case `SilentPaymentAddressError.encoding`. -/

namespace Winnow

inductive SilentPaymentAddressError where
  /-- not a bech32m string (silent payment codes always use bech32m) -/
  | invalidEncoding
  | wrongHRP (expected actual : String)
  /-- BIP352 defines version 0; 1–31 are reserved -/
  | unsupportedVersion (version : Nat)
  /-- the payload must be 66 bytes: two compressed keys -/
  | invalidDataLength (count : Nat)
  | invalidPublicKey
  /-- `convertBits` refused the payload (Swift lets its `Bech32Error` escape) -/
  | encoding (e : Bech32Error)
  deriving Repr, BEq, Inhabited

def SilentPaymentAddressError.name : SilentPaymentAddressError → String
  | .invalidEncoding => "invalidEncoding" | .wrongHRP .. => "wrongHRP" | .unsupportedVersion _ => "unsupportedVersion"
  | .invalidDataLength _ => "invalidDataLength" | .invalidPublicKey => "invalidPublicKey"
  | .encoding e => e.name

/-- A BIP352 code: the receiver's compressed scan key and spend key (label-tweaked when the receiver handed
out a labeled code; senders treat it as opaque), and the HRP. -/
structure SilentPaymentAddress where
  scanKey : ByteArray
  spendKey : ByteArray
  hrp : String
  deriving BEq, Inhabited

namespace SilentPaymentAddress

def version : Nat := 0
/-- A v0 code is 117 characters; BIP352 suggests 1023 (not BIP173's 90) so later versions can grow. -/
def maxAddressLength : Nat := 1023

/-- Shaped like a code (`sp1` / `tsp1`, either case): routes text to this parser rather than the address
decoder. A shape check only. -/
def looksLikeCode (text : String) : Bool :=
  let lowered := text.trimAscii.toString.toLower
  lowered.startsWith "sp1" || lowered.startsWith "tsp1"

def isValidPublicKey (key : ByteArray) : Bool := key.size == 33 && (Keys.parsePublicKey key).toBool

def make (scanKey spendKey : ByteArray) (hrp : String) : Except SilentPaymentAddressError SilentPaymentAddress :=
  if isValidPublicKey scanKey && isValidPublicKey spendKey then .ok { scanKey, spendKey, hrp }
  else .error .invalidPublicKey

/-- The bech32m encoding (`sp1q…` / `tsp1q…`). -/
def encoded (a : SilentPaymentAddress) : Except Bech32Error String := do
  let data ← SegwitAddress.convertBits (a.scanKey ++ a.spendKey).toList 8 5 true
  Bech32.encode a.hrp ((version.toUInt8) :: data) .bech32m maxAddressLength

/-- Decodes and validates a code strictly: bech32m, version 0, 66 bytes of two valid compressed keys, and
`expectedHRP` when given. -/
def decode (s : String) (expectedHRP : Option String := none) :
    Except SilentPaymentAddressError SilentPaymentAddress := do
  let (hrp, data, enc) ← match Bech32.decode s maxAddressLength with
    | .ok r => pure r
    | .error _ => throw .invalidEncoding
  unless enc == .bech32m do throw .invalidEncoding
  if let some expected := expectedHRP then
    unless hrp == expected do throw (.wrongHRP expected hrp)
  let v := (data.head?.map (·.toNat)).getD 0
  unless v == version do throw (.unsupportedVersion v)
  let payload ← match SegwitAddress.convertBits data.tail 5 8 false with
    | .ok p => pure p
    | .error e => throw (.encoding e)
  unless payload.length == 66 do throw (.invalidDataLength payload.length)
  let bytes := ByteArray.mk payload.toArray
  make (bytes.extract 0 33) (bytes.extract 33 66) hrp

/-- `decode`, by the name the wallet's record validation uses. -/
def parse (s : String) (expectedHRP : Option String := none) : Except SilentPaymentAddressError SilentPaymentAddress :=
  decode s expectedHRP

end SilentPaymentAddress

namespace Keys

namespace SilentPaymentSending

inductive Error where
  | noEligibleInputs | inputKeysSumToZero | invalidInputHash | invalidTweak | tooManyRecipientsPerGroup
  | invalidPrivateKey | invalidRecipientKey
  deriving Repr, BEq, DecidableEq

def Error.name : Error → String
  | .noEligibleInputs => "noEligibleInputs" | .inputKeysSumToZero => "inputKeysSumToZero"
  | .invalidInputHash => "invalidInputHash" | .invalidTweak => "invalidTweak"
  | .tooManyRecipientsPerGroup => "tooManyRecipientsPerGroup" | .invalidPrivateKey => "invalidPrivateKey"
  | .invalidRecipientKey => "invalidRecipientKey"

abbrev SP := Except Error

/-- BIP352 K_max: recipients sharing one scan key. -/
def maxRecipientsPerGroup : Nat := 2323

/-- One input as the sender sees it. The wallet spends only P2TR key paths: `privateKey` is then the
BIP341-tweaked key of the output, and `scriptSig`/`witness` are empty (the witness does not exist yet when
the outputs are derived). -/
structure Input where
  /-- 32 bytes, internal (wire) byte order -/
  txid : ByteArray
  vout : UInt32
  prevoutScriptPubKey : ByteArray
  scriptSig : ByteArray := .empty
  witness : List ByteArray := []
  privateKey : ByteArray

/-- The outpoint as it is sorted and hashed: txid ‖ vout, both little-endian. -/
def Input.outpoint (i : Input) : ByteArray :=
  i.txid ++ ByteArray.mk #[i.vout.toUInt8, (i.vout >>> 8).toUInt8, (i.vout >>> 16).toUInt8, (i.vout >>> 24).toUInt8]

structure Context where
  /-- compressed public keys of the eligible inputs, in input order -/
  eligiblePublicKeys : List ByteArray
  /-- a = Σ aᵢ mod n (each P2TR aᵢ for the even-Y key) -/
  privateKeySum : ByteArray
  /-- hash_BIP0352/Inputs(outpoint_L ‖ A) -/
  inputHash : ByteArray

/-! ## Script templates -/

def isP2TR (s : ByteArray) : Bool := s.size == 34 && s[0]! == 0x51 && s[1]! == 0x20
def isP2WPKH (s : ByteArray) : Bool := s.size == 22 && s[0]! == 0x00 && s[1]! == 0x14
def isP2PKH (s : ByteArray) : Bool :=
  s.size == 25 && s[0]! == 0x76 && s[1]! == 0xA9 && s[2]! == 0x14 && s[23]! == 0x88 && s[24]! == 0xAC
def isP2SH (s : ByteArray) : Bool := s.size == 23 && s[0]! == 0xA9 && s[1]! == 0x14 && s[22]! == 0x87

/-! ## Scalars and points -/

def scalarZero : ByteArray := ByteArray.mk (Array.replicate 32 0)

def isValidScalar (s : ByteArray) : Bool := isValidSecret s

def isValidCompressedKey (k : ByteArray) : Bool := k.size == 33 && (parsePublicKey k).toBool

/-- lift_x validity: x < p and the even-Y point exists. -/
def isValidXonlyKey (k : ByteArray) : Bool := k.size == 32 && (parsePublicKey (ByteArray.mk #[0x02] ++ k)).toBool

/-- s·G, compressed (its first byte carries the parity of y). -/
def publicKeyPoint (s : ByteArray) : SP ByteArray :=
  if !isValidScalar s then throw .invalidPrivateKey
  else match publicKeyOf s with
    | .ok k => pure k
    | .error _ => throw .invalidPrivateKey

/-- (a + b) mod n; a zero operand passes the other through, a zero sum stays zero. -/
def scalarAdd (a b : ByteArray) : SP ByteArray :=
  if a == scalarZero then pure b
  else if b == scalarZero then pure a
  else if !isValidScalar a || !isValidScalar b then throw .invalidPrivateKey
  else
    let s := (Secp.fromBE a + Secp.fromBE b) % groupN
    pure (if s == 0 then scalarZero else Secp.toBE32 s)

def scalarMultiply (a b : ByteArray) : SP ByteArray :=
  if !isValidScalar a || !isValidScalar b then throw .invalidPrivateKey
  else pure (Secp.toBE32 ((Secp.fromBE a * Secp.fromBE b) % groupN))

def negate (s : ByteArray) : SP ByteArray :=
  if !isValidScalar s then throw .invalidPrivateKey
  else pure (Secp.toBE32 (privateNegate (Secp.fromBE s)))

/-! ## Which inputs count -/

/-- P2PKH: a 33-byte window slid over the scriptSig from the back; the first whose HASH160 is the
script's hash (finds the key even in malleated scriptSigs). -/
def p2pkhKey (script scriptSig : ByteArray) : Option ByteArray := Id.run do
  let hash := script.extract 3 23
  if scriptSig.size < 33 then return none
  let mut stop := scriptSig.size
  while stop ≥ 33 do
    let candidate := scriptSig.extract (stop - 33) stop
    if hash160 candidate == hash && isValidCompressedKey candidate then return some candidate
    stop := stop - 1
  return none

/-- P2SH-P2WPKH: the redeem script (the scriptSig without its push) is P2WPKH; the key is the last
witness item. -/
def p2shP2wpkhKey (scriptSig : ByteArray) (witness : List ByteArray) : Option ByteArray :=
  if !isP2WPKH (scriptSig.extract 1 scriptSig.size) then none
  else match witness.getLast? with
    | some key => if isValidCompressedKey key then some key else none
    | none => none

def p2wpkhKey (witness : List ByteArray) : Option ByteArray :=
  match witness.getLast? with
  | some key => if isValidCompressedKey key then some key else none
  | none => none

/-- P2TR: the x-only output key, as its even-Y compressed form. A script-path spend whose internal key is
the NUMS point H is skipped; an empty witness (the sender, before signing) is a key-path spend. -/
def p2trKey (script : ByteArray) (witness : List ByteArray) : Option ByteArray := Id.run do
  let mut stack := witness
  -- a last item starting with 0x50 is the annex
  if stack.length > 1 && (stack.getLast?.bind (·[0]?)) == some 0x50 then stack := stack.dropLast
  if stack.length > 1 then
    if let some controlBlock := stack.getLast? then
      if controlBlock.size ≥ 33 && controlBlock.extract 1 33 == Taproot.unspendableInternalKey then return none
  let outputKey := script.extract 2 script.size
  if !isValidXonlyKey outputKey then return none
  return some (ByteArray.mk #[0x02] ++ outputKey)

/-- The public key an input contributes, or none when its type is not on BIP352's list (P2TR, P2WPKH,
P2SH-P2WPKH, P2PKH; compressed keys only). -/
def eligiblePublicKey (script scriptSig : ByteArray) (witness : List ByteArray) : Option ByteArray :=
  if isP2PKH script then p2pkhKey script scriptSig
  else if isP2SH script then p2shP2wpkhKey scriptSig witness
  else if isP2WPKH script then p2wpkhKey witness
  else if isP2TR script then p2trKey script witness
  else none

def Input.eligiblePublicKey (i : Input) : Option ByteArray :=
  SilentPaymentSending.eligiblePublicKey i.prevoutScriptPubKey i.scriptSig i.witness

/-! ## Deriving the outputs -/

/-- Lexicographic order of byte strings (a prefix first), as Swift's `lexicographicallyPrecedes`. -/
def bytesLess (a b : ByteArray) : Bool := a.toList < b.toList

/-- The eligible inputs, a (each P2TR key for its even-Y point first; a = 0 fails) and the input hash over
the smallest outpoint of all inputs and A = a·G. -/
def context (inputs : List Input) : SP Context := do
  let mut keys : Array ByteArray := #[]
  let mut sum := scalarZero
  for input in inputs do
    let some key := input.eligiblePublicKey | continue
    let mut secret := input.privateKey
    if isP2TR input.prevoutScriptPubKey then
      if (← publicKeyPoint secret)[0]! == 0x03 then secret ← negate secret
    sum ← scalarAdd sum secret
    keys := keys.push key
  if keys.isEmpty then throw .noEligibleInputs
  if sum == scalarZero then throw .inputKeysSumToZero
  let aggregate ← publicKeyPoint sum
  let smallest := (inputs.map (·.outpoint)).foldl (fun m o => if bytesLess o m then o else m)
    ((inputs.head?.map (·.outpoint)).getD .empty)
  let inputHash := taggedHash "BIP0352/Inputs" (smallest ++ aggregate)
  if !isValidScalar inputHash then throw .invalidInputHash
  return { eligiblePublicKeys := keys.toList, privateKeySum := sum, inputHash }

/-- ecdh_shared_secret = input_hash · a · B_scan, compressed. -/
def sharedSecret (c : Context) (scanKey : ByteArray) : SP ByteArray := do
  let scan ← match parsePublicKey scanKey with
    | .ok p => pure p
    | .error _ => throw .invalidRecipientKey
  let scalar ← scalarMultiply c.inputHash c.privateKeySum
  match publicMultiply scan scalar with
  | .ok p => pure (serializeCompressed p)
  | .error _ => throw .invalidRecipientKey

/-- One output: t_k = hash_BIP0352/SharedSecret(ser_P(ecdh) ‖ ser32(k)), P = B_m + t_k·G, as a P2TR
scriptPubKey (ser32 big-endian). -/
def outputScript (secret spendKey : ByteArray) (k : UInt32) : SP ByteArray := do
  let spend ← match parsePublicKey spendKey with
    | .ok p => pure p
    | .error _ => throw .invalidRecipientKey
  let kBytes := ByteArray.mk #[(k >>> 24).toUInt8, (k >>> 16).toUInt8, (k >>> 8).toUInt8, k.toUInt8]
  let tweak := taggedHash "BIP0352/SharedSecret" (secret ++ kBytes)
  if !isValidScalar tweak then throw .invalidTweak
  let out ← match pointOfSecret (Secp.fromBE tweak) >>= fun t => combine [spend, t] with
    | .ok p => pure p
    | .error _ => throw .invalidRecipientKey
  return ByteArray.mk #[0x51, 0x20] ++ xonlyBytes out

/-- One P2TR scriptPubKey per recipient, in recipient order. Recipients are grouped by scan key (one ECDH
per group, groups in first-appearance order); within a group k counts up, so paying one code twice gives
two outputs. -/
def outputScripts (inputs : List Input) (recipients : List SilentPaymentAddress) : SP (List ByteArray) := do
  let c ← context inputs
  let mut groups : Array (ByteArray × Array Nat) := #[]
  for (r, index) in recipients.zipIdx do
    match groups.findIdx? (·.1 == r.scanKey) with
    | some g => groups := groups.modify g fun (s, is) => (s, is.push index)
    | none => groups := groups.push (r.scanKey, #[index])
  if groups.any (·.2.size > maxRecipientsPerGroup) then throw .tooManyRecipientsPerGroup
  let mut scripts : Array ByteArray := Array.replicate recipients.length .empty
  for (scanKey, indices) in groups do
    let secret ← sharedSecret c scanKey
    for (index, k) in indices.toList.zipIdx do
      scripts := scripts.set! index (← outputScript secret recipients[index]!.spendKey k.toUInt32)
  return scripts.toList

end SilentPaymentSending

/-! ## The payment kind (`Transactions/SilentPayment.swift`) -/

/-- A payment to a code: its output script is derived at signing time, once coin selection has fixed the
inputs. -/
structure SilentPayment where
  amount : Int64
  address : SilentPaymentAddress

namespace SilentPayment

/-- `sp` on mainnet, `tsp` on every test network (regtest has none of its own and takes the test one). -/
def hrp (mainnet : Bool) : String := if mainnet then "sp" else "tsp"

/-- The P2TR placeholder that keeps coin selection's fee math exact before the script is derived. -/
def sizingScriptPubKey : ByteArray := ByteArray.mk #[0x51, 0x20] ++ ByteArray.mk (Array.replicate 32 0)

end SilentPayment

end Keys
end Winnow
