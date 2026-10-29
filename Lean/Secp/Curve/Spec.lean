import Secp.Field.Ops

/-! # The specification: secp256k1 over the integers modulo P

Points are affine pairs over `F := Fin P` or the point at infinity, added by the textbook chord
and tangent rules with field division. Scalar multiplication is left-to-right double-and-add over
the 256 bits of the scalar. Nothing here is executed; it is what `Secp.Curve.Jacobian` is proven
to compute.

**The one assumption.** Division needs every non-zero element to be invertible, which is the
statement that `P` is prime. It is not proven here (a Pratt certificate needs factors of `P - 1`
that are out of reach for this repository's tooling), so it enters as the class `FieldP`, taken
as a hypothesis by every theorem that needs it, never as an axiom. -/

namespace Secp.Spec

abbrev F := Fin P

/-- `P` is prime, as the statement the proofs use: every non-zero element has an inverse. -/
class FieldP : Prop where
  inv_exists : ∀ a : F, a ≠ 0 → ∃ w, a * w = 1

open Classical in
/-- Field inverse (0 for 0). -/
noncomputable def inv (a : F) : F := if h : ∃ w, a * w = 1 then Classical.choose h else 0

theorem mul_inv [FieldP] {a : F} (h : a ≠ 0) : a * inv a = 1 := by
  have he := FieldP.inv_exists a h
  simp only [inv, he, dite_true]
  exact Classical.choose_spec he

theorem mul_eq_zero [FieldP] {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have := mul_inv ha
    calc b = (a * inv a) * b := by rw [this]; grind
      _ = inv a * (a * b) := by grind
      _ = 0 := by rw [h]; grind

theorem two_ne_zero : (2 : F) ≠ 0 := by decide
theorem three_ne_zero : (3 : F) ≠ 0 := by decide

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

theorem G_onCurve : OnCurve G := by
  show Gy * Gy = Gx * Gx * Gx + 7
  decide

/-! ## The law keeps points on the curve -/

theorem tangent_onCurve [FieldP] {x y : F} (h : y * y = x * x * x + 7) (hy : y ≠ 0) :
    OnCurve (tangent x y) := by
  have h2y : 2 * y ≠ 0 := by
    intro h0; rcases mul_eq_zero h0 with h | h
    · exact two_ne_zero h
    · exact hy h
  have hw := mul_inv h2y
  simp only [tangent, OnCurve]
  generalize inv (2 * y) = w at hw
  grind

theorem chord_onCurve [FieldP] {x1 y1 x2 y2 : F} (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7) (hx : x1 ≠ x2) : OnCurve (chord x1 y1 x2 y2) := by
  have hd : x2 - x1 ≠ 0 := fun h0 => hx (by grind)
  have hw := mul_inv hd
  simp only [chord, OnCurve]
  generalize inv (x2 - x1) = w at hw
  grind

theorem add_onCurve [FieldP] {p q : Point} (hp : OnCurve p) (hq : OnCurve q) : OnCurve (add p q) := by
  match p, q with
  | .inf, q => exact hq
  | .pt x y, .inf => exact hp
  | .pt x1 y1, .pt x2 y2 =>
    simp only [add]
    split
    · split
      · rename_i _ h; exact tangent_onCurve hp h.2
      · trivial
    · rename_i h; exact chord_onCurve hp hq h

theorem smul_onCurve [FieldP] (k : Nat) {p : Point} (hp : OnCurve p) : OnCurve (smul k p) := by
  unfold smul
  generalize (List.range 256).reverse = bits
  suffices ∀ r, OnCurve r → OnCurve (bits.foldl (fun r i => if k.testBit i then add (add r r) p else add r r) r) from
    this _ trivial
  induction bits with
  | nil => intro r hr; exact hr
  | cons i is ih =>
    intro r hr
    simp only [List.foldl_cons]
    apply ih
    split
    · exact add_onCurve (add_onCurve hr hr) hp
    · exact add_onCurve hr hr

end Secp.Spec
