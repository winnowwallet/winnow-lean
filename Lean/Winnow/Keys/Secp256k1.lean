import Secp.Keys
import Winnow.Crypto

/-! # secp256k1 as WalletCore uses it through P256K

WalletCore reaches libsecp256k1 through the P256K Swift package (`Signing.PrivateKey`, `Signing.PublicKey`,
`Schnorr.PrivateKey`, `Schnorr.XonlyKey`, `Schnorr.SchnorrSignature`). These functions give the same
answers and the same refusals, on top of the proven `Secp` library (no curve arithmetic here).

P256K's errors are `secp256k1Error`: `incorrectKeySize` (a key of the wrong byte count, checked before
libsecp256k1 is called), `incorrectParameterSize` (a signature of the wrong length) and
`underlyingCryptoError` (libsecp256k1 returned 0). Several WalletCore functions let these escape.

Where P256K passes a buffer to libsecp256k1 without checking its length (tweaks, auxiliary randomness,
x-only keys), libsecp256k1 reads 32 bytes regardless: shorter buffers are out-of-bounds reads in the
original. Here they are refused with `incorrectParameterSize`, and the lockstep never sends them.

**Not constant-time** (unlike libsecp256k1, which these functions replace): BIP340 signing (Winnow makes no ECDSA signatures), tweaks
and public-key derivation run on `Secp`'s GMP-backed `Nat` scalars and its bit-by-bit scalar multiplication,
so their timing depends on the secret key and nonce. They are correct by proof and by lockstep against
P256K. BIP340 nonces come from the key, the message and fresh auxiliary randomness
(`Signer.randomAuxiliaryRand`), so signing one message twice does not repeat a nonce. That is acceptable for
what Winnow does with it: low-volume signing the user approves, on the user's own device, where no one can
trigger operations on demand or time them. Do not reuse it in servers, signing services, shared hosts, or
anything that signs on someone else's request (SECURITY.md, "Timing side channels"). -/

namespace Winnow.Keys
open Secp

inductive P256KError where
  | incorrectKeySize | incorrectParameterSize | underlyingCryptoError
  deriving Repr, DecidableEq, Inhabited

def P256KError.name : P256KError → String
  | .incorrectKeySize => "incorrectKeySize"
  | .incorrectParameterSize => "incorrectParameterSize"
  | .underlyingCryptoError => "underlyingCryptoError"

abbrev PK := Except P256KError

/-- A finite curve point in affine coordinates. -/
abbrev Point := Fq × Fq

/-- The group order. -/
def groupN : Nat := Secp.Spec.N

/-- `secp256k1_ec_seckey_verify`: 32 bytes, nonzero, below the order. -/
def isValidSecret (b : ByteArray) : Bool :=
  b.size == 32 && (let d := fromBE b; d != 0 && d < groupN)

/-- `P256K.Signing.PrivateKey(dataRepresentation:)`: the scalar of a 32-byte secret. -/
def secretOf (b : ByteArray) : PK Nat :=
  if b.size != 32 then throw .incorrectKeySize
  else
    let d := fromBE b
    if d == 0 || d ≥ groupN then throw .underlyingCryptoError else pure d

def lift {α} (r : Secp.R α) : PK α :=
  match r with
  | .ok a => .ok a
  | .error _ => .error .underlyingCryptoError

/-- Affine form of a Jacobian result; infinity is `none`. -/
def affine (j : Jac) : PK (Option Point) :=
  match j.toAffine? with
  | some .inf => pure none
  | some (.pt x y) => pure (some (x, y))
  | none => throw .underlyingCryptoError

def toA : Option Point → APoint
  | none => .inf
  | some (x, y) => .pt x y

/-- What compiled code runs for `addOpt`, `mulOpt` and `mulGen` (`Secp.Fast`, as `Secp.mulG` does). -/
def affineFast (j : Secp.Fast.J) : PK (Option Point) :=
  if j.Z.isZero then pure none else
  match j.toA? with | some a => pure (some (Secp.ofFastA a)) | none => throw .underlyingCryptoError

def addOptFast (a b : Option Point) : PK (Option Point) :=
  match a, b with
  | none, none => pure none
  | some p, none | none, some p => pure (some p)
  | some p, some q => affineFast ((Secp.Fast.J.inf.addA (Secp.toFastA p.1 p.2)).addA (Secp.toFastA q.1 q.2))

def mulOptFast (k : Nat) (p : Point) : PK (Option Point) :=
  match Secp.Fast.mulPtJ (k % groupN) (Secp.toFastA p.1 p.2) with
  | some j => affineFast j
  | none => throw .underlyingCryptoError

def mulGenFast (k : Nat) : PK (Option Point) := affineFast (Secp.Fast.mulGJ (k % groupN))

/-- `a + b`, either possibly infinity. -/
@[implemented_by addOptFast]
def addOpt (a b : Option Point) : PK (Option Point) := affine ((Jac.inf.add (toA a)).add (toA b))

/-- `k·p`; `none` for infinity. -/
@[implemented_by mulOptFast]
def mulOpt (k : Nat) (p : Point) : PK (Option Point) := affine (smulJ k (.pt p.1 p.2))

@[implemented_by mulGenFast]
def mulGen (k : Nat) : PK (Option Point) := affine (smulJ k Secp.Gpt)

/-- `d·G` for a valid secret. -/
def pointOfSecret (d : Nat) : PK Point := lift (pubOf d)

def serializeCompressed (p : Point) : ByteArray := Secp.compressed p.1 p.2
def serializeUncompressed (p : Point) : ByteArray :=
  ByteArray.mk #[4] ++ toBE32 p.1.toNat ++ toBE32 p.2.toNat
def xonlyBytes (p : Point) : ByteArray := toBE32 p.1.toNat
def hasOddY (p : Point) : Bool := p.2.isOdd

/-- `secp256k1_ec_pubkey_parse` of a 65-byte key: `04 x y`, or hybrid `06`/`07` whose tag matches y's parity. -/
def parseUncompressed (b : ByteArray) : Option Point :=
  let tag := b[0]!
  if !(tag == 4 || tag == 6 || tag == 7) then none else
  let x := fromBE (b.extract 1 33)
  let y := fromBE (b.extract 33 65)
  if x ≥ P || y ≥ P then none else
  let fx := Fq.ofNat x
  let fy := Fq.ofNat y
  if fy * fy != fx * fx * fx + 7 then none
  else if (tag == 6 || tag == 7) && (fy.isOdd != (tag == 7)) then none
  else some (fx, fy)

/-- `P256K.Signing.PublicKey(dataRepresentation:format:)`: exactly 33 (compressed) or 65 (uncompressed)
bytes, then `secp256k1_ec_pubkey_parse`. -/
def parsePublicKey (b : ByteArray) (compressed : Bool := true) : PK Point :=
  if b.size != (if compressed then 33 else 65) then throw .incorrectKeySize
  else if compressed then lift (Secp.parseCompressed b)
  else match parseUncompressed b with
    | some p => pure p
    | none => throw .underlyingCryptoError

/-- `PrivateKey.publicKey.dataRepresentation`, compressed or uncompressed. -/
def publicKeyOf (secret : ByteArray) (compressed : Bool := true) : PK ByteArray := do
  let p ← pointOfSecret (← secretOf secret)
  return if compressed then serializeCompressed p else serializeUncompressed p

/-- `PublicKey.xonly`: the x coordinate and whether y is odd. -/
def xonlyOf (p : Point) : ByteArray × Bool := (xonlyBytes p, hasOddY p)

/-- A 32-byte tweak scalar as libsecp256k1 reads it (`overflow` refused by the callers). -/
def tweak32 (t : ByteArray) : PK Nat :=
  if t.size != 32 then throw .incorrectParameterSize else pure (fromBE t)

/-! ## Signing keys (`ECDSA+Tweak.swift`) -/

/-- `Signing.PrivateKey.add`: `secp256k1_ec_seckey_tweak_add`; a tweak ≥ n or a zero sum fails. -/
def privateAdd (d : Nat) (tw : ByteArray) : PK Nat := do
  let t ← tweak32 tw
  if t ≥ groupN then throw .underlyingCryptoError
  let s := (d + t) % groupN
  if s == 0 then throw .underlyingCryptoError
  return s

/-- `Signing.PrivateKey.multiply`: `secp256k1_ec_seckey_tweak_mul`; a zero tweak or one ≥ n fails. -/
def privateMultiply (d : Nat) (tw : ByteArray) : PK Nat := do
  let t ← tweak32 tw
  if t == 0 || t ≥ groupN then throw .underlyingCryptoError
  return (d * t) % groupN

/-- `PrivateKey.negation`. -/
def privateNegate (d : Nat) : Nat := (groupN - d) % groupN

/-- `Signing.PublicKey.add`: `t·G + P` (`secp256k1_ec_pubkey_tweak_add`); infinity fails. -/
def publicAdd (p : Point) (tw : ByteArray) : PK Point := do
  let t ← tweak32 tw
  if t ≥ groupN then throw .underlyingCryptoError
  match ← addOpt (← mulGen t) (some p) with
  | some q => pure q
  | none => throw .underlyingCryptoError

/-- `Signing.PublicKey.multiply`: `t·P` (`secp256k1_ec_pubkey_tweak_mul`). -/
def publicMultiply (p : Point) (tw : ByteArray) : PK Point := do
  let t ← tweak32 tw
  if t == 0 || t ≥ groupN then throw .underlyingCryptoError
  match ← mulOpt t p with
  | some q => pure q
  | none => throw .underlyingCryptoError

/-- `PublicKey.negation`. -/
def publicNegate (p : Point) : Point := (p.1, -p.2)

/-- `PublicKey.combine`: the sum of all keys (`secp256k1_ec_pubkey_combine`); infinity fails. -/
def combine (ps : List Point) : PK Point := do
  let mut acc : Option Point := none
  for p in ps do acc ← addOpt acc (some p)
  match acc with
  | some q => pure q
  | none => throw .underlyingCryptoError

/-! ## Schnorr keys (`Schnorr+Tweak.swift`, `Schnorr+Signature.swift`) -/

/-- `secp256k1_xonly_pubkey_parse` of the first 32 bytes (P256K passes the buffer unchecked). -/
def parseXonly (b : ByteArray) : PK Point :=
  if b.size < 32 then throw .incorrectParameterSize
  else lift (Secp.parseXOnly (b.extract 0 32))

/-- `Schnorr.XonlyKey.add`: `t·G + lift_x(x)`, returned as x-only bytes and the parity of y. -/
def xonlyAdd (x : ByteArray) (tw : ByteArray) : PK (ByteArray × Bool) := do
  let p ← parseXonly x
  let t ← tweak32 tw
  if t ≥ groupN then throw .underlyingCryptoError
  match ← addOpt (← mulGen t) (some p) with
  | some q => pure (xonlyOf q)
  | none => throw .underlyingCryptoError

/-- `Schnorr.PrivateKey.add`: `secp256k1_keypair_xonly_tweak_add` (negate the secret when its point has
odd y, then add). -/
def keypairXonlyAdd (d : Nat) (tw : ByteArray) : PK Nat := do
  let _ ← tweak32 tw
  lift (Secp.secretAddXOnly d tw)

/-- `Schnorr.PrivateKey.signature(message:auxiliaryRand:)`: BIP340 with 32 bytes of auxiliary randomness,
over a message of any length. `crypto-test` holds it to BIP340's test vectors signature for signature. -/
def schnorrSign (d : Nat) (msg aux : ByteArray) : PK ByteArray :=
  if aux.size != 32 then throw .incorrectParameterSize else lift (Secp.sign msg d aux)

/-- `SchnorrSignature(dataRepresentation:)` then `XonlyKey.isValid(_:for:)`. -/
def schnorrVerify (xonly msg sig : ByteArray) : PK Bool := do
  if sig.size != 64 then throw .incorrectParameterSize
  if xonly.size < 32 then throw .incorrectParameterSize
  match Secp.verify sig msg (xonly.extract 0 32) with
  | .ok v => pure v
  | .error _ => pure false

end Winnow.Keys
