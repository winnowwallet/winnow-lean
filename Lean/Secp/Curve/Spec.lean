/-! # The specification: secp256k1 over the integers modulo P

Points are affine pairs over `F := Fin P` or the point at infinity, added by the textbook chord
and tangent rules with field division. Scalar multiplication is left-to-right double-and-add over
the 256 bits of the scalar. Nothing here is executed; it is the pure mathematical definition
everything else is held to.

Primality of `P` and `N` and the abelian group law of `Point` are proved unconditionally in
`Secp/Proofs/Primes.lean` and `Secp/Proofs/Group.lean`. -/

namespace Secp

/-- The field's modulus, 2²⁵⁶ − 2³² − 977. -/
def P : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

instance : NeZero P := ⟨by decide⟩

end Secp

namespace Secp.Spec

abbrev F := Fin P

open Classical in
/-- Field inverse (0 for 0). -/
noncomputable def inv (a : F) : F := if h : ∃ w, a * w = 1 then Classical.choose h else 0

inductive Point where
  | inf
  | pt (x y : F)
  deriving DecidableEq

def OnCurve : Point → Prop
  | .inf => True
  | .pt x y => y * y = x * x * x + 7

def neg : Point → Point
  | .inf => .inf
  | .pt x y => .pt x (-y)

/-- The tangent at `(x, y)`: slope `3x² / 2y`. -/
noncomputable def tangent (x y : F) : Point :=
  let l := 3 * x * x * inv (2 * y)
  let x3 := l * l - 2 * x
  .pt x3 (l * (x - x3) - y)

/-- The chord through `(x1, y1)` and `(x2, y2)`: slope `(y2 - y1) / (x2 - x1)`. -/
noncomputable def chord (x1 y1 x2 y2 : F) : Point :=
  let l := (y2 - y1) * inv (x2 - x1)
  let x3 := l * l - x1 - x2
  .pt x3 (l * (x1 - x3) - y1)

/-- The group law. -/
noncomputable def add : Point → Point → Point
  | .inf, q => q
  | p, .inf => p
  | .pt x1 y1, .pt x2 y2 =>
    if x1 = x2 then (if y1 = y2 ∧ y1 ≠ 0 then tangent x1 y1 else .inf) else chord x1 y1 x2 y2

/-- `k · p` by left-to-right double-and-add over bits 255 … 0. -/
noncomputable def smul (k : Nat) (p : Point) : Point :=
  (List.range 256).reverse.foldl (fun r i => if k.testBit i then add (add r r) p else add r r) .inf

def Gx : F := ⟨0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, by decide⟩
def Gy : F := ⟨0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, by decide⟩
def G : Point := .pt Gx Gy

/-- The group order. -/
def N : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

end Secp.Spec
