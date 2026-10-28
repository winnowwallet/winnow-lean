import Secp.Curve.Jacobian
import Secp.Sha256

/-! # Keys, tweaks and BIP340, as NativeSecp256k1 exposes them

The same inputs, outputs and refusal reasons as `Secp256k1.PrivateKey`, `PublicKey`, `XOnlyKey`
and `Schnorr` in `Sources/NativeSecp256k1`, so the two can be compared answer for answer.
Scalars are integers below `N`, computed with `Nat`; points go through the proven Jacobian code.
`internal` reports a field inverse that failed its own check, which `P` being prime rules out.

**Not constant-time.** Correct by proof (`sign_verifies`, `verify_sound` and the rest of `Secp.Proofs.Gate`)
and by lockstep against libsecp256k1, but secret scalars are Lean `Nat`s, GMP-backed big numbers whose
running time depends on their values, and every scalar multiplication goes through `smulJ`, which branches
on each bit of the scalar (`Secp.Curve.Jacobian`). Signing, tweaking and public-key derivation therefore
leak timing. That is acceptable for what Winnow does with it: low-volume signing the user approves, on the
user's own device, where no one can trigger operations on demand or time them. Do not reuse it in servers,
signing services, shared hosts, or anything that signs on someone else's request (SECURITY.md, "Timing side
channels"). -/

namespace Secp
open Spec (N)

inductive Err where
  | invalidPrivateKey | invalidPublicKey | invalidTweak | invalidResult
  | invalidAuxiliaryRand | signingFailed | internal
  deriving Repr, DecidableEq

def Err.name : Err → String
  | .invalidPrivateKey => "invalidPrivateKey" | .invalidPublicKey => "invalidPublicKey"
  | .invalidTweak => "invalidTweak" | .invalidResult => "invalidResult"
  | .invalidAuxiliaryRand => "invalidAuxiliaryRand" | .signingFailed => "signingFailed"
  | .internal => "internal"

abbrev R := Except Err

def Gpt : APoint := .pt (Fq.ofNat Spec.Gx.val) (Fq.ofNat Spec.Gy.val)

def mulG (k : Nat) : R APoint :=
  match smul? k Gpt with | some q => pure q | none => throw .internal

def mulPt (k : Nat) (p : APoint) : R APoint :=
  match smul? k p with | some q => pure q | none => throw .internal

/-- `k·G + p`, through one Jacobian addition. -/
def mulGAdd (k : Nat) (p : APoint) : R APoint :=
  match ((smulJ k Gpt).add p).toAffine? with | some q => pure q | none => throw .internal

/-- Exactly 32 bytes below `N`. -/
def scalar? (b : ByteArray) : Option Nat :=
  if b.size = 32 ∧ fromBE b < N then some (fromBE b) else none

def secret (b : ByteArray) : R Nat :=
  match scalar? b with
  | some d => if d = 0 then throw .invalidPrivateKey else pure d
  | none => throw .invalidPrivateKey

def tweak (b : ByteArray) : R Nat :=
  match scalar? b with | some t => pure t | none => throw .invalidTweak

def negN (d : Nat) : Nat := (N - d) % N

def pubOf (d : Nat) : R (Fq × Fq) := do
  match ← mulG d with
  | .pt x y => pure (x, y)
  | .inf => throw .internal

def compressed (x y : Fq) : ByteArray :=
  (ByteArray.mk #[if y.isOdd then 3 else 2]) ++ toBE32 x.toNat

/-- The even-y point with this x (`lift_x`), or `none` when `x ≥ P` or `x³ + 7` is not a square. -/
def liftX? (x : Nat) : Option (Fq × Fq) :=
  if x < P then
    let fx := Fq.ofNat x
    match (fx * fx * fx + 7).sqrt? with
    | some y => some (fx, if y.isOdd then -y else y)
    | none => none
  else none

def parseCompressed (b : ByteArray) : R (Fq × Fq) :=
  if b.size = 33 ∧ (b[0]! = 2 ∨ b[0]! = 3) then
    match liftX? (fromBE (b.extract 1 33)) with
    | some (x, y) => pure (x, if b[0]! = 3 then -y else y)
    | none => throw .invalidPublicKey
  else throw .invalidPublicKey

def parseXOnly (b : ByteArray) : R (Fq × Fq) :=
  if b.size = 32 then
    match liftX? (fromBE b) with | some p => pure p | none => throw .invalidPublicKey
  else throw .invalidPublicKey

/-- `PrivateKey.adding`: `(d + t) mod N`, refusing a zero result. -/
def secretAdd (d : Nat) (tb : ByteArray) : R Nat :=
  match tweak tb with
  | .error e => .error e
  | .ok t => let s := (d + t) % N; if s = 0 then .error .invalidResult else .ok s

/-- `PrivateKey.addingXOnly`: negate `d` first when `d·G` has an odd y. -/
def secretAddXOnly (d : Nat) (tb : ByteArray) : R Nat :=
  match pubOf d with
  | .error e => .error e
  | .ok (_, y) =>
    match tweak tb with
    | .error e => .error e
    | .ok t =>
      let s := ((if y.isOdd then negN d else d) + t) % N
      if s = 0 then .error .invalidResult else .ok s

/-- `PublicKey.adding`: `t·G + K`, refusing infinity. -/
def pointAdd (x y : Fq) (tb : ByteArray) : R (Fq × Fq) := do
  let t ← tweak tb
  match ← mulGAdd t (.pt x y) with
  | .pt x' y' => pure (x', y')
  | .inf => throw .invalidResult

/-- `XOnlyKey.adding`: `t·G + lift_x(x)` with its parity. -/
def xonlyAdd (x y : Fq) (tb : ByteArray) : R (Fq × Fq) := do
  let t ← tweak tb
  let even := if y.isOdd then -y else y
  match ← mulGAdd t (.pt x even) with
  | .pt x' y' => pure (x', y')
  | .inf => throw .invalidResult

def xorBytes (a b : ByteArray) : ByteArray :=
  ⟨(a.toList.zip b.toList).toArray.map fun (u, v) => u ^^^ v⟩

def hashMod (b : ByteArray) : Nat := fromBE b % N

def challenge (rx px m : ByteArray) : Nat := hashMod (Sha256.tagged "BIP0340/challenge" (rx ++ px ++ m))

def negPt : APoint → APoint
  | .inf => .inf
  | .pt x y => .pt x (-y)

/-- BIP340 verification of a 64-byte signature under a 32-byte x-only key:
`R = s·G - e·P` must be finite, have an even y and the x the signature names. -/
def verify (sig m xb : ByteArray) : R Bool :=
  if sig.size ≠ 64 then .ok false else
  match (if xb.size = 32 then liftX? (fromBE xb) else none) with
  | none => .ok false
  | some (px, py) =>
    let r := fromBE (sig.extract 0 32)
    let s := fromBE (sig.extract 32 64)
    if r ≥ P ∨ s ≥ N then .ok false else
    let e := challenge (toBE32 r) (toBE32 px.toNat) m
    match mulPt e (.pt px py) with
    | .error err => .error err
    | .ok eP =>
      match mulGAdd s (negPt eP) with
      | .error err => .error err
      | .ok .inf => .ok false
      | .ok (.pt x y) => .ok (!y.isOdd && x.toNat == r)

/-- The signature of BIP340 signing and the x-only key it is made under, before the final self-check. -/
def signRaw (m : ByteArray) (d0 : Nat) (aux : ByteArray) : R (ByteArray × ByteArray) :=
  if aux.size ≠ 32 then .error .invalidAuxiliaryRand else
  match pubOf d0 with
  | .error e => .error e
  | .ok (px, py) =>
    let d := if py.isOdd then negN d0 else d0
    let pxb := toBE32 px.toNat
    let t := xorBytes (toBE32 d) (Sha256.tagged "BIP0340/aux" aux)
    let k0 := hashMod (Sha256.tagged "BIP0340/nonce" (t ++ pxb ++ m))
    if k0 = 0 then .error .signingFailed else
    match mulG k0 with
    | .error e => .error e
    | .ok .inf => .error .signingFailed
    | .ok (.pt rx ry) =>
      let k := if ry.isOdd then negN k0 else k0
      let rxb := toBE32 rx.toNat
      let e := challenge rxb pxb m
      .ok (rxb ++ toBE32 ((k + e * d) % N), pxb)

/-- BIP340 signing with the auxiliary randomness given; the signature is verified under the
signer's x-only key before it is returned. -/
def sign (m : ByteArray) (d0 : Nat) (aux : ByteArray) : R ByteArray :=
  match signRaw m d0 aux with
  | .error e => .error e
  | .ok (sig, pxb) =>
    match verify sig m pxb with
    | .ok true => .ok sig
    | .ok false => .error .signingFailed
    | .error e => .error e

end Secp
