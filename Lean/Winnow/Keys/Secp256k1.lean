import SecpCt.Keys
import Winnow.Crypto

/-! # secp256k1 as the wallet uses it

Every curve operation the wallet does goes through here, and from here to `SecpCt` (`Lean/SecpCt/`): one
implementation, on machine words, each operation proved against the curve as specified
(`SecpCt/Gate.lean`). There is no arithmetic in this file. What it adds is the shape the rest of the wallet
calls: which input is refused and with which error.

The names and the refusals are those of the P256K Swift package the wallet was written against
(`Signing.PrivateKey`, `Signing.PublicKey`, `Schnorr.PrivateKey`, `Schnorr.XonlyKey`): `incorrectKeySize`
(a key of the wrong byte count), `incorrectParameterSize` (a signature, tweak or randomness of the wrong
length) and `underlyingCryptoError` (libsecp256k1 would have returned 0).

Two types keep the rest of the wallet from the two mistakes that matter:

  - a `Point` is made only by a function that has checked it is on the curve (the parsers) or computed it
    from points that were. The addition formulas are right only on this curve, and `publicMultiply`
    multiplies a point someone else supplied by a number that is secret;
  - a `Secret` is made only from 32 bytes that are a key as they stand (1 to N − 1), is never a `Nat`, and
    cannot be printed or compared. What is done with one (the public point, a tweak added, a signature) is
    done by code that does the same work whatever it is.

Timing: see SECURITY.md, "Timing side channels", for what is and is not checked about the compiled code. -/

namespace Winnow.Keys

inductive P256KError where
  | incorrectKeySize | incorrectParameterSize | underlyingCryptoError
  deriving Repr, DecidableEq, Inhabited

/-- Swift's case name, which the errors and texts that carry this one read (crypto-test `errorNames`). -/
def P256KError.name : P256KError → String
  | .incorrectKeySize => "incorrectKeySize"
  | .incorrectParameterSize => "incorrectParameterSize"
  | .underlyingCryptoError => "underlyingCryptoError"

abbrev PK := Except P256KError

/-- A point of the curve, never the point at infinity. -/
abbrev Point := SecpCt.Affine

/-- A secret key: a number from 1 to N − 1. -/
structure Secret where
  private mk ::
  scalar : SecpCt.Sc

def found {α} (o : Option α) : PK α :=
  match o with
  | some a => pure a
  | none => throw .underlyingCryptoError

/-- `secp256k1_ec_seckey_verify`: 32 bytes, nonzero, below the order. -/
def isValidSecret (b : ByteArray) : Bool := b.size == 32 && SecpCt.Sc.isKey b == 1

/-- `P256K.Signing.PrivateKey(dataRepresentation:)`: the key 32 bytes are. -/
def secretOf (b : ByteArray) : PK Secret :=
  if b.size != 32 then throw .incorrectKeySize
  else if SecpCt.Sc.isKey b == 1 then pure ⟨SecpCt.Sc.ofBytes b⟩ else throw .underlyingCryptoError

/-- The key as 32 bytes. -/
def Secret.bytes (d : Secret) : ByteArray := d.scalar.bytes

/-- `d·G`. -/
def pointOfSecret (d : Secret) : PK Point := found (SecpCt.publicPoint d.scalar)

def serializeCompressed (p : Point) : ByteArray := p.compressed
def serializeUncompressed (p : Point) : ByteArray := p.uncompressed
def xonlyBytes (p : Point) : ByteArray := p.xBytes
def hasOddY (p : Point) : Bool := p.isOdd

/-- `P256K.Signing.PublicKey(dataRepresentation:format:)`: exactly 33 (compressed) or 65 (uncompressed, or
hybrid `06`/`07` whose first byte matches y's parity) bytes that are a point of the curve. -/
def parsePublicKey (b : ByteArray) (compressed : Bool := true) : PK Point :=
  if b.size != (if compressed then 33 else 65) then throw .incorrectKeySize
  else found (if compressed then SecpCt.parseCompressed b else SecpCt.parseUncompressed b)

/-- `PrivateKey.publicKey.dataRepresentation`, compressed or uncompressed. -/
def publicKeyOf (secret : ByteArray) (compressed : Bool := true) : PK ByteArray := do
  let p ← pointOfSecret (← secretOf secret)
  return if compressed then serializeCompressed p else serializeUncompressed p

/-- `PublicKey.xonly`: the x coordinate and whether y is odd. -/
def xonlyOf (p : Point) : ByteArray × Bool := (xonlyBytes p, hasOddY p)

/-- A 32-byte tweak: a number below N (libsecp256k1 refuses one that overflows). -/
def tweak32 (t : ByteArray) : PK SecpCt.Sc :=
  if t.size != 32 then throw .incorrectParameterSize else found (SecpCt.scalar? t)

/-! ## Signing keys (`ECDSA+Tweak.swift`) -/

/-- `Signing.PrivateKey.add`: `secp256k1_ec_seckey_tweak_add`; a tweak ≥ N or a zero sum fails. -/
def privateAdd (d : Secret) (tw : ByteArray) : PK Secret := do
  let s := SecpCt.Sc.add d.scalar (← tweak32 tw)
  if s.isZero == 1 then throw .underlyingCryptoError else pure ⟨s⟩

/-- `PrivateKey.negation`: `N − d`. -/
def privateNegate (d : Secret) : Secret := ⟨SecpCt.Sc.neg d.scalar⟩

/-- The sum of two keys modulo N; a zero sum fails. -/
def Secret.add (a b : Secret) : PK Secret :=
  let s := SecpCt.Sc.add a.scalar b.scalar
  if s.isZero == 1 then throw .underlyingCryptoError else pure ⟨s⟩

/-- The product of two keys modulo N. -/
def Secret.multiply (a b : Secret) : PK Secret :=
  let s := SecpCt.Sc.mul a.scalar b.scalar
  if s.isZero == 1 then throw .underlyingCryptoError else pure ⟨s⟩

/-- `Signing.PublicKey.add`: `t·G + P` (`secp256k1_ec_pubkey_tweak_add`); infinity fails. -/
def publicAdd (p : Point) (tw : ByteArray) : PK Point := do
  found (SecpCt.pointAdd p (← tweak32 tw))

/-- `Signing.PublicKey.multiply`: `t·P` (`secp256k1_ec_pubkey_tweak_mul`), for a `t` from 1 to N − 1 that
may be secret. -/
def publicMultiply (p : Point) (tw : ByteArray) : PK Point := do
  let t ← (secretOf tw).mapError fun
    | .incorrectKeySize => .incorrectParameterSize
    | e => e
  found (SecpCt.pointMul t.scalar p)

/-- `PublicKey.combine`: the sum of all keys (`secp256k1_ec_pubkey_combine`); infinity fails. -/
def combine (ps : List Point) : PK Point := found (SecpCt.combine ps)

/-! ## Schnorr keys (`Schnorr+Tweak.swift`, `Schnorr+Signature.swift`) -/

/-- `secp256k1_xonly_pubkey_parse` of the first 32 bytes. -/
def parseXonly (b : ByteArray) : PK Point :=
  if b.size < 32 then throw .incorrectParameterSize
  else found (SecpCt.parseXOnly (b.extract 0 32))

/-- `Schnorr.XonlyKey.add`: `t·G + lift_x(x)`, returned as x-only bytes and the parity of y. -/
def xonlyAdd (x : ByteArray) (tw : ByteArray) : PK (ByteArray × Bool) := do
  let p ← parseXonly x
  return xonlyOf (← found (SecpCt.pointAdd p (← tweak32 tw)))

/-- `Schnorr.PrivateKey.add`: `secp256k1_keypair_xonly_tweak_add` (negate the secret when its point has
odd y, then add). -/
def keypairXonlyAdd (d : Secret) (tw : ByteArray) : PK Secret := do
  let t ← tweak32 tw
  let s := SecpCt.Sc.add (SecpCt.evenKey d.scalar) t
  if s.isZero == 1 then throw .underlyingCryptoError else pure ⟨s⟩

/-- `Schnorr.PrivateKey.signature(message:auxiliaryRand:)`: BIP 340 with 32 bytes of auxiliary randomness,
over a message of any length. The signature is verified under the signer's own key before it is returned.
`crypto-test` holds it to BIP 340's test vectors signature for signature. -/
def schnorrSign (d : Secret) (msg aux : ByteArray) : PK ByteArray :=
  if aux.size != 32 then throw .incorrectParameterSize else found (SecpCt.signVerified d.bytes msg aux)

/-- `SchnorrSignature(dataRepresentation:)` then `XonlyKey.isValid(_:for:)`. -/
def schnorrVerify (xonly msg sig : ByteArray) : PK Bool := do
  if sig.size != 64 then throw .incorrectParameterSize
  if xonly.size < 32 then throw .incorrectParameterSize
  return SecpCt.verify sig msg (xonly.extract 0 32)

end Winnow.Keys
