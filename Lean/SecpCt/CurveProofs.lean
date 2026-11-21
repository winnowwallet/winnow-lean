import SecpCt.Proofs
import SecpCt.ScalarProofs
import SecpCt.Point
import Secp.Proofs.Group

/-! # What is proved about the curve

That multiplying the generator by a scalar gives the point the specification says: `mulGenerator_rep`. The
specification is winnow's (`Secp.Spec`): points as pairs of field elements or the point at infinity, added
by the chord and tangent rules, and `k · G` by double-and-add over the bits of `k`.

It is built in four steps.

1. The field elements of `SecpCt` are mapped into the specification's field and the field's operations shown
   to be that field's (`toF_add`, `toF_sub`, `toF_mul`).
2. `Point.add` is shown to compute the complete addition formulas of Renes, Costello and Batina
   (`add_formulas`).
3. Those formulas are shown to add points (`formulas_add`): whenever the coordinates going in stand for two
   points of the curve, the coordinates coming out stand for their sum. The same statement covers two
   different points, a point and itself, a point and its negative, and the point at infinity on either side.
   This is the paper's theorem, proved here for this curve by checking each case's algebra.
4. `mulGenerator` is shown to be the double-and-add ladder over the scalar's bits, the choice by mask being
   the choice by the bit (`mulGenerator_ladder`), and each bit to be that bit of the number
   (`Sc.bit_testBit`).

The step from three coordinates to the two a public key is made of is proved as well (`affine_point`,
`public_point`): it divides by raising to the power P − 2, justified unconditionally by `Secp.Primes.P_prime`.

Bytes are in `SecpCt/BytesProofs.lean`, the public key from bytes to bytes in `SecpCt/KeyProofs.lean`, and
signing in `SecpCt/SignProofs.lean`.

Nothing that runs imports this file; `SecpCt/Gate.lean` does. -/

namespace SecpCt
open Secp.Spec (F OnCurve)
open Secp

theorem P_eq : P = Secp.P := by decide

/-- An element is in its one right form: below P. -/
def Fe.Valid (a : Fe) : Prop := a.toNat < P

/-- The element as a member of the field the specification is written over. -/
def Fe.toF (a : Fe) : F := Fin.ofNat Secp.P a.toNat

theorem Fe.toF_val (a : Fe) : a.toF.val = a.toNat % P := by
  rw [P_eq]; rfl

theorem toF_mul (a b : Fe) : (Fe.mul a b).toF = a.toF * b.toF := by
  apply Fin.ext
  rw [Fin.val_mul, Fe.toF_val, Fe.toF_val, Fe.toF_val, mul_spec, ← P_eq, Nat.mod_mod, ← Nat.mul_mod]

theorem valid_mul (a b : Fe) : (Fe.mul a b).Valid := mul_lt a b

theorem toF_add (a b : Fe) (ha : a.Valid) (hb : b.Valid) : (Fe.add a b).toF = a.toF + b.toF := by
  apply Fin.ext
  rw [Fin.val_add, Fe.toF_val, Fe.toF_val, Fe.toF_val, add_spec a b ha hb, ← P_eq, Nat.mod_mod, ← Nat.add_mod]

theorem toF_sub (a b : Fe) (ha : a.Valid) (hb : b.Valid) : (Fe.sub a b).toF = a.toF - b.toF := by
  apply Fin.ext
  rw [Fin.val_sub, Fe.toF_val, Fe.toF_val, Fe.toF_val, sub_spec a b ha hb, ← P_eq, Nat.mod_mod,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  congr 1
  have := ha; have := hb
  simp only [Fe.Valid] at *
  omega

theorem valid_add (a b : Fe) (ha : a.Valid) (hb : b.Valid) : (Fe.add a b).Valid := add_lt a b ha hb
theorem valid_sub (a b : Fe) (ha : a.Valid) (hb : b.Valid) : (Fe.sub a b).Valid := sub_lt a b ha hb

theorem toF_b3 : Point.b3.toF = 21 := by decide

/-- `Point.add` computes the complete addition formulas of Renes, Costello and Batina for y² = x³ + 7, in the
field the specification is written over. -/
theorem add_formulas (p q : Point) (hpx : p.x.Valid) (hpy : p.y.Valid) (hpz : p.z.Valid)
    (hqx : q.x.Valid) (hqy : q.y.Valid) (hqz : q.z.Valid) :
    (Point.add p q).x.toF = (p.x.toF * q.y.toF + q.x.toF * p.y.toF) * (p.y.toF * q.y.toF - 21 * p.z.toF * q.z.toF)
        - 21 * (p.y.toF * q.z.toF + q.y.toF * p.z.toF) * (p.x.toF * q.z.toF + q.x.toF * p.z.toF)
    ∧ (Point.add p q).y.toF = (p.y.toF * q.y.toF + 21 * p.z.toF * q.z.toF) * (p.y.toF * q.y.toF - 21 * p.z.toF * q.z.toF)
        + 63 * p.x.toF * q.x.toF * (p.x.toF * q.z.toF + q.x.toF * p.z.toF)
    ∧ (Point.add p q).z.toF = (p.y.toF * q.z.toF + q.y.toF * p.z.toF) * (p.y.toF * q.y.toF + 21 * p.z.toF * q.z.toF)
        + 3 * p.x.toF * q.x.toF * (p.x.toF * q.y.toF + q.x.toF * p.y.toF) := by
  simp only [Point.add]
  simp only [toF_add, toF_sub, toF_mul, toF_b3, valid_add, valid_mul, hpx, hpy, hpz, hqx, hqy, hqz]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Whatever is added, the coordinates of the sum are below P. -/
theorem valid_point_add (p q : Point) : (Point.add p q).x.Valid ∧ (Point.add p q).y.Valid ∧ (Point.add p q).z.Valid := by
  simp only [Point.add, valid_add, valid_sub, valid_mul, and_self]

/-- `Point.double` computes the complete doubling formulas, in the field the specification is written over. -/
theorem double_formulas (p : Point) :
    (Point.double p).x.toF = 2 * p.x.toF * p.y.toF * (p.y.toF * p.y.toF - 63 * p.z.toF * p.z.toF)
    ∧ (Point.double p).y.toF = (p.y.toF * p.y.toF - 63 * p.z.toF * p.z.toF) * (p.y.toF * p.y.toF + 21 * p.z.toF * p.z.toF)
        + 168 * p.y.toF * p.y.toF * p.z.toF * p.z.toF
    ∧ (Point.double p).z.toF = 8 * p.y.toF * p.y.toF * p.y.toF * p.z.toF := by
  simp only [Point.double]
  simp (maxDischargeDepth := 8) only [toF_add, toF_sub, toF_mul, toF_b3, valid_add, valid_mul]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Whatever is doubled, the coordinates of the result are below P. -/
theorem valid_point_double (p : Point) :
    (Point.double p).x.Valid ∧ (Point.double p).y.Valid ∧ (Point.double p).z.Valid := by
  simp (maxDischargeDepth := 8) only [Point.double, valid_add, valid_mul, and_self]

/-! ## Multiplying a point -/

/-- `choose` takes the first point under a mask from a bit of 1, the second from a bit of 0. -/
theorem Point.choose_one (p q : Point) : Point.choose (mask 1) p q = p := by
  simp only [Point.choose, Fe.choose_one]

theorem Point.choose_zero (p q : Point) : Point.choose (mask 0) p q = q := by
  simp only [Point.choose, Fe.choose_zero]

/-- A bit of a scalar is 0 or 1. -/
theorem Sc.bit_cases (k : Sc) (i : Nat) : k.bit i = 0 ∨ k.bit i = 1 := by
  simp only [Sc.bit]
  generalize ((if i < 64 then k.a0 else if i < 128 then k.a1 else if i < 192 then k.a2 else k.a3)
    >>> (i % 64).toUInt64) = x
  exact and_one_cases x

/-- What one bit of the scalar does: double, and add the point if the bit is set. -/
def ladderStep (k : Sc) (p : Point) (acc : Point) (i : Nat) : Point :=
  if k.bit (255 - i) = 1 then Point.add (Point.double acc) p else Point.double acc

/-- `mul` is the double-and-add ladder over the scalar's 256 bits, most significant first. The choice by mask
is the choice by the bit. -/
theorem mul_ladder (k : Sc) (p : Point) :
    Point.mul k p = (List.range' 0 256).foldl (ladderStep k p) Point.infinity := by
  have body : (fun (i : Nat) (acc : Point) => (pure (ForInStep.yield
      (Point.choose (mask (k.bit (255 - i))) (Point.add (Point.double acc) p) (Point.double acc)))
        : Id (ForInStep Point))) = fun i acc => pure (ForInStep.yield (ladderStep k p acc i)) := by
    funext i acc
    simp only [ladderStep]
    rcases Sc.bit_cases k (255 - i) with h | h <;> rw [h]
    · rw [Point.choose_zero]; rfl
    · rw [Point.choose_one]; rfl
  simp only [Point.mul]
  simp [-List.foldl_cons, body]

/-- `mulPublic` is the same ladder: it leaves out exactly the additions the mask would have thrown away. -/
theorem mulPublic_ladder (k : Sc) (p : Point) :
    Point.mulPublic k p = (List.range' 0 256).foldl (ladderStep k p) Point.infinity := by
  have body : (fun (i : Nat) (acc : Point) => (if k.bit (255 - i) = 1 then
        pure (ForInStep.yield (Point.add (Point.double acc) p)) else pure (ForInStep.yield (Point.double acc))
        : Id (ForInStep Point))) = fun i acc => pure (ForInStep.yield (ladderStep k p acc i)) := by
    funext i acc
    simp only [ladderStep]
    split <;> rfl
  simp only [Point.mulPublic]
  simp [-List.foldl_cons, body]

/-! ## The formulas, as formulas -/

def RX (X1 Y1 Z1 X2 Y2 Z2 : F) : F :=
  (X1 * Y2 + X2 * Y1) * (Y1 * Y2 - 21 * Z1 * Z2) - 21 * (Y1 * Z2 + Y2 * Z1) * (X1 * Z2 + X2 * Z1)
def RY (X1 Y1 Z1 X2 Y2 Z2 : F) : F :=
  (Y1 * Y2 + 21 * Z1 * Z2) * (Y1 * Y2 - 21 * Z1 * Z2) + 63 * X1 * X2 * (X1 * Z2 + X2 * Z1)
def RZ (X1 Y1 Z1 X2 Y2 Z2 : F) : F :=
  (Y1 * Z2 + Y2 * Z1) * (Y1 * Y2 + 21 * Z1 * Z2) + 3 * X1 * X2 * (X1 * Y2 + X2 * Y1)

/-- Three coordinates stand for a point of the specification: (0 : Y : 0) with Y ≠ 0 for the point at
infinity, and otherwise (X : Y : Z) with Z ≠ 0 for the point (X/Z, Y/Z). -/
def RepF (X Y Z : F) : Spec.Point → Prop
  | .inf => X = 0 ∧ Z = 0 ∧ Y ≠ 0
  | .pt x y => ∃ w, Z * w = 1 ∧ x = X * w ∧ y = Y * w

theorem ne_zero_of_mul_eq_one {a w : F} (h : a * w = 1) : a ≠ 0 := by
  intro e
  rw [e] at h
  have : (0 : F) * w = 0 := by grind
  rw [this] at h
  exact absurd h (by decide)

theorem mul_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  Spec.mul_ne_zero ha hb

/-- Multiplying all three coordinates by something that is not zero leaves the point they stand for. -/
theorem repF_scale (s X Y Z : F) (hs : s ≠ 0) (c : Spec.Point) (h : RepF X Y Z c) :
    RepF (s * X) (s * Y) (s * Z) c := by
  cases c with
  | inf =>
    obtain ⟨hx, hz, hy⟩ := h
    refine ⟨by rw [hx]; grind, by rw [hz]; grind, mul_ne_zero hs hy⟩
  | pt x y =>
    obtain ⟨w, hw, hx, hy⟩ := h
    have hi := Spec.mul_inv hs
    generalize Spec.inv s = u at hi
    clear hs
    refine ⟨w * u, by grind, by grind, by grind⟩

/-- The formulas are of degree two in each point's coordinates. -/
theorem R_scaled (x1 y1 Z1 x2 y2 Z2 : F) :
    RX (x1 * Z1) (y1 * Z1) Z1 (x2 * Z2) (y2 * Z2) Z2 = (Z1 * Z2) * (Z1 * Z2) * RX x1 y1 1 x2 y2 1
    ∧ RY (x1 * Z1) (y1 * Z1) Z1 (x2 * Z2) (y2 * Z2) Z2 = (Z1 * Z2) * (Z1 * Z2) * RY x1 y1 1 x2 y2 1
    ∧ RZ (x1 * Z1) (y1 * Z1) Z1 (x2 * Z2) (y2 * Z2) Z2 = (Z1 * Z2) * (Z1 * Z2) * RZ x1 y1 1 x2 y2 1 := by
  simp only [RX, RY, RZ]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-! ## Two different points: the chord -/

/-- The third coordinate is, up to the cube of the difference of the x's, the y of P − Q. So it is zero only
if P − Q has y = 0, which no point has. -/
theorem chord_Z (x1 y1 x2 y2 v : F) (h1 : y1 * y1 = x1 * x1 * x1 + 7) (h2 : y2 * y2 = x2 * x2 * x2 + 7)
    (hv : (x2 - x1) * v = 1) :
    RZ x1 y1 1 x2 y2 1 * (v * v * v) =
      (-y2 - y1) * v * (x1 - ((-y2 - y1) * v * ((-y2 - y1) * v) - x1 - x2)) - y1 := by
  simp only [RZ]
  grind

theorem chord_X (x1 y1 x2 y2 v : F) (h1 : y1 * y1 = x1 * x1 * x1 + 7) (h2 : y2 * y2 = x2 * x2 * x2 + 7)
    (hv : (x2 - x1) * v = 1) :
    RX x1 y1 1 x2 y2 1 = ((y2 - y1) * v * ((y2 - y1) * v) - x1 - x2) * RZ x1 y1 1 x2 y2 1 := by
  simp only [RX, RZ]
  grind

theorem chord_Y (x1 y1 x2 y2 v : F) (h1 : y1 * y1 = x1 * x1 * x1 + 7) (h2 : y2 * y2 = x2 * x2 * x2 + 7)
    (hv : (x2 - x1) * v = 1) :
    RY x1 y1 1 x2 y2 1 = ((y2 - y1) * v * (x1 - ((y2 - y1) * v * ((y2 - y1) * v) - x1 - x2)) - y1) * RZ x1 y1 1 x2 y2 1 := by
  simp only [RY, RZ]
  grind

theorem affine_chord (x1 y1 x2 y2 : F) (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7) (hx : x1 ≠ x2) :
    RepF (RX x1 y1 1 x2 y2 1) (RY x1 y1 1 x2 y2 1) (RZ x1 y1 1 x2 y2 1) (Spec.chord x1 y1 x2 y2) := by
  have hd : x2 - x1 ≠ 0 := fun h0 => hx (by grind)
  have hv := Spec.mul_inv hd
  have h2' : (-y2) * (-y2) = x2 * x2 * x2 + 7 := by grind
  have difference := Spec.chord_onCurve h1 h2' hx
  simp only [Spec.chord, OnCurve] at difference
  have yd := Spec.onCurve_y_ne_zero difference
  have hz := chord_Z x1 y1 x2 y2 _ h1 h2 hv
  have hX := chord_X x1 y1 x2 y2 _ h1 h2 hv
  have hY := chord_Y x1 y1 x2 y2 _ h1 h2 hv
  simp only [Spec.chord, RepF]
  generalize Spec.inv (x2 - x1) = v at *
  have hZ : RZ x1 y1 1 x2 y2 1 ≠ 0 := by
    intro e
    rw [e] at hz
    exact yd (by rw [← hz]; clear yd difference hd hx hv; grind)
  have hw := Spec.mul_inv hZ
  generalize Spec.inv (RZ x1 y1 1 x2 y2 1) = w at hw
  clear hZ difference yd hz h1 h2 h2' hv hd hx
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hX]; grind
  · rw [hY]; grind

/-! ## A point and itself: the tangent -/

theorem tangent_Z (x y : F) (h : y * y = x * x * x + 7) : RZ x y 1 x y 1 = 8 * (y * y * y) := by
  simp only [RZ]
  grind

theorem tangent_X (x y u : F) (h : y * y = x * x * x + 7) (hu : 2 * y * u = 1) :
    RX x y 1 x y 1 = (3 * x * x * u * (3 * x * x * u) - 2 * x) * RZ x y 1 x y 1 := by
  simp only [RX, RZ]
  grind

theorem tangent_Y (x y u : F) (h : y * y = x * x * x + 7) (hu : 2 * y * u = 1) :
    RY x y 1 x y 1 = (3 * x * x * u * (x - (3 * x * x * u * (3 * x * x * u) - 2 * x)) - y) * RZ x y 1 x y 1 := by
  simp only [RY, RZ]
  grind

theorem affine_tangent (x y : F) (h : y * y = x * x * x + 7) (hy : y ≠ 0) :
    RepF (RX x y 1 x y 1) (RY x y 1 x y 1) (RZ x y 1 x y 1) (Spec.tangent x y) := by
  have h2y : 2 * y ≠ 0 := mul_ne_zero Spec.two_ne_zero hy
  have hu := Spec.mul_inv h2y
  have hX := tangent_X x y _ h hu
  have hY := tangent_Y x y _ h hu
  simp only [Spec.tangent, RepF]
  generalize Spec.inv (2 * y) = u at *
  have hZ : RZ x y 1 x y 1 ≠ 0 := by
    rw [tangent_Z x y h]
    exact mul_ne_zero (by decide) (mul_ne_zero (mul_ne_zero hy hy) hy)
  have hw := Spec.mul_inv hZ
  generalize Spec.inv (RZ x y 1 x y 1) = w at hw
  clear hZ h hu h2y hy
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hX]; grind
  · rw [hY]; grind

/-! ## A point and its negative: the point at infinity -/

/-- The second coordinate is, up to the cube of 2y, the y of 2P. So it is not zero. -/
theorem opposite_Y (x y u : F) (h : y * y = x * x * x + 7) (hu : 2 * y * u = 1) :
    RY x y 1 x (-y) 1 * (u * u * u) = 3 * x * x * u * (x - (3 * x * x * u * (3 * x * x * u) - 2 * x)) - y := by
  simp only [RY]
  grind

theorem affine_opposite (x y : F) (h : y * y = x * x * x + 7) :
    RepF (RX x y 1 x (-y) 1) (RY x y 1 x (-y) 1) (RZ x y 1 x (-y) 1) .inf := by
  have hy := Spec.onCurve_y_ne_zero h
  have h2y : 2 * y ≠ 0 := mul_ne_zero Spec.two_ne_zero hy
  have hu := Spec.mul_inv h2y
  have double := Spec.tangent_onCurve h hy
  simp only [Spec.tangent, OnCurve] at double
  have yt := Spec.onCurve_y_ne_zero double
  have hY := opposite_Y x y _ h hu
  generalize Spec.inv (2 * y) = u at *
  refine ⟨by clear hy h2y yt double hu; simp only [RX]; grind,
          by clear hy h2y yt double hu; simp only [RZ]; grind, ?_⟩
  intro e
  rw [e] at hY
  exact yt (by rw [← hY]; clear hy h2y yt double hu e; grind)

/-! ## All of it -/

/-- The complete formulas add points: if the coordinates stand for two points of the curve, what the
formulas give stands for their sum as the specification defines it. One statement for every case, which is
what "complete" means. -/
theorem formulas_add {X1 Y1 Z1 X2 Y2 Z2 : F} {a b : Spec.Point}
    (ha : OnCurve a) (hb : OnCurve b) (ra : RepF X1 Y1 Z1 a) (rb : RepF X2 Y2 Z2 b) :
    RepF (RX X1 Y1 Z1 X2 Y2 Z2) (RY X1 Y1 Z1 X2 Y2 Z2) (RZ X1 Y1 Z1 X2 Y2 Z2) (Spec.add a b) := by
  match a, b with
  | .inf, .inf =>
    obtain ⟨rfl, rfl, hy1⟩ := ra
    obtain ⟨rfl, rfl, hy2⟩ := rb
    refine ⟨by clear hy1 hy2; simp only [RX]; grind, by clear hy1 hy2; simp only [RZ]; grind, ?_⟩
    have : RY 0 Y1 0 0 Y2 0 = (Y1 * Y2) * (Y1 * Y2) := by clear hy1 hy2; simp only [RY]; grind
    rw [this]
    exact mul_ne_zero (mul_ne_zero hy1 hy2) (mul_ne_zero hy1 hy2)
  | .inf, .pt x2 y2 =>
    obtain ⟨rfl, rfl, hy1⟩ := ra
    have hy2 : Y2 ≠ 0 := by
      obtain ⟨w, _, _, hy⟩ := rb
      intro e
      exact Spec.onCurve_y_ne_zero hb (by rw [hy, e]; clear hy1; grind)
    have scaled := repF_scale (Y1 * Y1 * Y2) X2 Y2 Z2 (mul_ne_zero (mul_ne_zero hy1 hy1) hy2) _ rb
    have eX : RX 0 Y1 0 X2 Y2 Z2 = Y1 * Y1 * Y2 * X2 := by clear hy1 hy2 scaled rb hb; simp only [RX]; grind
    have eY : RY 0 Y1 0 X2 Y2 Z2 = Y1 * Y1 * Y2 * Y2 := by clear hy1 hy2 scaled rb hb; simp only [RY]; grind
    have eZ : RZ 0 Y1 0 X2 Y2 Z2 = Y1 * Y1 * Y2 * Z2 := by clear hy1 hy2 scaled rb hb; simp only [RZ]; grind
    rw [eX, eY, eZ]
    exact scaled
  | .pt x1 y1, .inf =>
    obtain ⟨rfl, rfl, hy2⟩ := rb
    have hy1 : Y1 ≠ 0 := by
      obtain ⟨w, _, _, hy⟩ := ra
      intro e
      exact Spec.onCurve_y_ne_zero ha (by rw [hy, e]; clear hy2; grind)
    have scaled := repF_scale (Y2 * Y2 * Y1) X1 Y1 Z1 (mul_ne_zero (mul_ne_zero hy2 hy2) hy1) _ ra
    have eX : RX X1 Y1 Z1 0 Y2 0 = Y2 * Y2 * Y1 * X1 := by clear hy1 hy2 scaled ra ha; simp only [RX]; grind
    have eY : RY X1 Y1 Z1 0 Y2 0 = Y2 * Y2 * Y1 * Y1 := by clear hy1 hy2 scaled ra ha; simp only [RY]; grind
    have eZ : RZ X1 Y1 Z1 0 Y2 0 = Y2 * Y2 * Y1 * Z1 := by clear hy1 hy2 scaled ra ha; simp only [RZ]; grind
    rw [eX, eY, eZ]
    exact scaled
  | .pt x1 y1, .pt x2 y2 =>
    obtain ⟨w1, hw1, hx1, hy1⟩ := ra
    obtain ⟨w2, hw2, hx2, hy2⟩ := rb
    have eX1 : X1 = x1 * Z1 := by grind
    have eY1 : Y1 = y1 * Z1 := by grind
    have eX2 : X2 = x2 * Z2 := by grind
    have eY2 : Y2 = y2 * Z2 := by grind
    obtain ⟨sX, sY, sZ⟩ := R_scaled x1 y1 Z1 x2 y2 Z2
    rw [eX1, eY1, eX2, eY2, sX, sY, sZ]
    have hs : (Z1 * Z2) * (Z1 * Z2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ne_zero_of_mul_eq_one hw1) (ne_zero_of_mul_eq_one hw2))
        (mul_ne_zero (ne_zero_of_mul_eq_one hw1) (ne_zero_of_mul_eq_one hw2))
    apply repF_scale _ _ _ _ hs
    simp only [OnCurve] at ha hb
    simp only [Spec.add]
    by_cases hx : x1 = x2
    · subst hx
      simp only [↓reduceIte]
      by_cases hy : y1 = y2 ∧ y1 ≠ 0
      · obtain ⟨rfl, hy⟩ := hy
        simp only [hy, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        exact affine_tangent x1 y1 ha hy
      · simp only [hy, ↓reduceIte]
        have opposite : y2 = -y1 := by
          rcases Spec.eq_or_neg_of_eq_x ha hb with same | opp
          · exact absurd ⟨same, Spec.onCurve_y_ne_zero ha⟩ hy
          · exact opp
        rw [opposite]
        exact affine_opposite x1 y1 ha
    · simp only [hx, ↓reduceIte]
      exact affine_chord x1 y1 x2 y2 ha hb hx

/-! ## The code -/

/-- A point of `SecpCt` stands for a point of the specification: its coordinates are below P and, read in the
specification's field, stand for it. -/
def Rep (p : Point) (a : Spec.Point) : Prop :=
  p.x.Valid ∧ p.y.Valid ∧ p.z.Valid ∧ RepF p.x.toF p.y.toF p.z.toF a

/-- `Point.add` adds: on points that stand for two points of the curve, it gives a point that stands for
their sum. -/
theorem rep_add {p q : Point} {a b : Spec.Point} (ha : OnCurve a) (hb : OnCurve b)
    (hp : Rep p a) (hq : Rep q b) : Rep (Point.add p q) (Spec.add a b) := by
  obtain ⟨px, py, pz, rp⟩ := hp
  obtain ⟨qx, qy, qz, rq⟩ := hq
  obtain ⟨vx, vy, vz⟩ := valid_point_add p q
  obtain ⟨fx, fy, fz⟩ := add_formulas p q px py pz qx qy qz
  refine ⟨vx, vy, vz, ?_⟩
  rw [fx, fy, fz]
  exact formulas_add ha hb rp rq

/-- A point that stands for a point of the curve satisfies the curve's equation in its three coordinates:
Y²Z = X³ + 7Z³. -/
theorem repF_curve {X Y Z : F} {a : Spec.Point} (ha : OnCurve a) (r : RepF X Y Z a) :
    Y * Y * Z = X * X * X + 7 * Z * Z * Z := by
  match a, ha, r with
  | .inf, _, ⟨hx, hz, _⟩ =>
    rw [hx, hz]
    simp only [Fin.mul_zero, Fin.add_zero]
  | .pt x y, ha, ⟨w, hw, hx, hy⟩ =>
    have curve : y * y = x * x * x + 7 := ha
    subst hx hy
    grind

/-- On the curve, the doubling formulas are the addition formulas for a point and itself. -/
theorem double_is_add (X Y Z : F) (h : Y * Y * Z = X * X * X + 7 * Z * Z * Z) :
    2 * X * Y * (Y * Y - 63 * Z * Z) = RX X Y Z X Y Z
    ∧ (Y * Y - 63 * Z * Z) * (Y * Y + 21 * Z * Z) + 168 * Y * Y * Z * Z = RY X Y Z X Y Z
    ∧ 8 * Y * Y * Y * Z = RZ X Y Z X Y Z := by
  have cube : X * X * X = Y * Y * Z - 7 * Z * Z * Z := by grind
  simp only [RX, RY, RZ]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- `Point.double` doubles: on a point that stands for a point of the curve, it gives a point that stands for
that point added to itself. -/
theorem rep_double {p : Point} {a : Spec.Point} (ha : OnCurve a) (hp : Rep p a) :
    Rep (Point.double p) (Spec.add a a) := by
  obtain ⟨_, _, _, rp⟩ := hp
  obtain ⟨vx, vy, vz⟩ := valid_point_double p
  obtain ⟨fx, fy, fz⟩ := double_formulas p
  obtain ⟨ex, ey, ez⟩ := double_is_add _ _ _ (repF_curve ha rp)
  refine ⟨vx, vy, vz, ?_⟩
  rw [fx, fy, fz, ex, ey, ez]
  exact formulas_add ha ha rp rp

theorem zero_toNat : Fe.zero.toNat = 0 := by
  simp only [Fe.zero, Fe.toNat, value, show (0 : UInt64).toNat = 0 from rfl]

theorem one_toNat : Fe.one.toNat = 1 := by
  simp only [Fe.one, Fe.toNat, value, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl]

theorem zero_toF : Fe.zero.toF = 0 := by
  rw [Fe.toF, zero_toNat]
  rfl

theorem one_toF : Fe.one.toF = 1 := by
  rw [Fe.toF, one_toNat]
  rfl

theorem zero_valid : Fe.zero.Valid := by
  rw [Fe.Valid, zero_toNat]
  decide

theorem one_valid : Fe.one.Valid := by
  rw [Fe.Valid, one_toNat]
  decide

theorem rep_infinity : Rep Point.infinity .inf := by
  refine ⟨zero_valid, one_valid, zero_valid, ?_⟩
  show Fe.zero.toF = 0 ∧ Fe.zero.toF = 0 ∧ Fe.one.toF ≠ 0
  rw [zero_toF, one_toF]
  decide

theorem rep_generator : Rep Point.generator Spec.G := by
  have gx : Point.generator.x.toNat = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 := by decide
  have gy : Point.generator.y.toNat = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 := by decide
  refine ⟨by rw [Fe.Valid, gx]; decide, by rw [Fe.Valid, gy]; decide, one_valid, 1, ?_, ?_, ?_⟩
  · show Fe.one.toF * 1 = 1
    rw [one_toF]
    decide
  · show Spec.Gx = Fin.ofNat Secp.P Point.generator.x.toNat * 1
    rw [gx]
    decide
  · show Spec.Gy = Fin.ofNat Secp.P Point.generator.y.toNat * 1
    rw [gy]
    decide

/-! ## The ladder -/

/-- A bit of a word, taken by shifting and masking, is that bit of the number. -/
theorem word_bit (w : UInt64) (s : Nat) (hs : s < 64) :
    ((w >>> s.toUInt64) &&& 1 = 1) ↔ w.toNat.testBit s = true := by
  have shift : s.toUInt64.toNat % 64 = s := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight, shift, show (1 : UInt64).toNat = 1 from rfl,
    Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq]

/-- A bit of a scalar is that bit of the number it stands for. -/
theorem Sc.bit_testBit (k : Sc) (j : Nat) (hj : j < 256) : (k.bit j = 1) ↔ k.toNat.testBit j = true := by
  have b0 := k.a0.toNat_lt; have b1 := k.a1.toNat_lt; have b2 := k.a2.toNat_lt
  have shape : k.toNat = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * k.a3.toNat + k.a2.toNat) + k.a1.toNat) + k.a0.toNat := by
    simp only [Sc.toNat, value, Nat.reducePow]
    omega
  rw [shape, Nat.testBit_two_pow_mul_add _ b0, Nat.testBit_two_pow_mul_add _ b1, Nat.testBit_two_pow_mul_add _ b2]
  simp only [Sc.bit]
  by_cases h0 : j < 64
  · simp only [h0, ↓reduceIte]
    rw [show j % 64 = j by omega]
    exact word_bit _ _ h0
  · by_cases h1 : j < 128
    · simp only [h0, h1, show j - 64 < 64 by omega, ↓reduceIte]
      rw [show j % 64 = j - 64 by omega]
      exact word_bit _ _ (by omega)
    · by_cases h2 : j < 192
      · simp only [h0, h1, h2, show ¬ (j - 64 < 64) by omega, show j - 64 - 64 < 64 by omega, ↓reduceIte]
        rw [show j % 64 = j - 64 - 64 by omega]
        exact word_bit _ _ (by omega)
      · simp only [h0, h1, h2, show ¬ (j - 64 < 64) by omega, show ¬ (j - 64 - 64 < 64) by omega, ↓reduceIte]
        rw [show j % 64 = j - 64 - 64 - 64 by omega]
        exact word_bit _ _ (by omega)

/-- Along the scalar's bits, the running point keeps standing for the specification's running point, for any
point of the curve being multiplied. -/
theorem ladder_rep (k : Sc) {p : Point} {a : Spec.Point} (ha : OnCurve a) (hp : Rep p a)
    (l : List Nat) (acc : Point) (r : Spec.Point) (hr : OnCurve r) (h : Rep acc r) :
    Rep (l.foldl (ladderStep k p) acc)
      (l.foldl (fun r i => if k.toNat.testBit (255 - i) then Spec.add (Spec.add r r) a else Spec.add r r) r) := by
  induction l generalizing acc r with
  | nil => exact h
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have doubled := rep_double hr h
    have onDoubled := Spec.add_onCurve hr hr
    by_cases bit : k.toNat.testBit (255 - i) = true
    · have set := (Sc.bit_testBit k (255 - i) (by omega)).mpr bit
      simp only [ladderStep, set, bit, ↓reduceIte]
      exact ih _ _ (Spec.add_onCurve onDoubled ha) (rep_add onDoubled ha doubled hp)
    · have clear : ¬ (k.bit (255 - i) = 1) := fun e => bit ((Sc.bit_testBit k (255 - i) (by omega)).mp e)
      simp only [ladderStep, clear, bit, ↓reduceIte]
      exact ih _ _ onDoubled doubled

/-- The 256 bits, most significant first, as the specification lists them and as the code counts them. -/
theorem ladder_bits : (List.range 256).reverse = (List.range' 0 256).map (fun i => 255 - i) := by decide +kernel

/-- **Multiplying a point.** For a point that stands for a point `a` of the curve, what `mul` returns stands
for `k · a` as the specification defines it. -/
theorem mul_rep (k : Sc) {p : Point} {a : Spec.Point} (ha : OnCurve a) (hp : Rep p a) :
    Rep (Point.mul k p) (Spec.smul k.toNat a) := by
  rw [mul_ladder, Spec.smul, ladder_bits, List.foldl_map]
  exact ladder_rep k ha hp _ _ _ trivial rep_infinity

/-- The same for the multiplication that is for scalars that are not secret. -/
theorem mulPublic_rep (k : Sc) {p : Point} {a : Spec.Point} (ha : OnCurve a) (hp : Rep p a) :
    Rep (Point.mulPublic k p) (Spec.smul k.toNat a) := by
  rw [mulPublic_ladder, Spec.smul, ladder_bits, List.foldl_map]
  exact ladder_rep k ha hp _ _ _ trivial rep_infinity

/-- Multiplying the generator: the point `mulGenerator` returns stands for `k · G` as the specification
defines it. -/
theorem mulGenerator_rep (k : Sc) :
    Rep (Point.mulGenerator k) (Spec.smul k.toNat Spec.G) :=
  mul_rep k Spec.G_onCurve rep_generator

/-! ## A point from two coordinates, and a point negated -/

/-- Two coordinates below P, with 1 for the third, stand for the point they name. -/
theorem rep_ofAffine {x y : Fe} (hx : x.Valid) (hy : y.Valid) : Rep (Point.ofAffine x y) (.pt x.toF y.toF) := by
  refine ⟨hx, hy, one_valid, 1, ?_, ?_, ?_⟩
  · show Fe.one.toF * 1 = 1
    rw [one_toF]
    decide
  · show x.toF = x.toF * 1
    clear hx hy; grind
  · show y.toF = y.toF * 1
    clear hx hy; grind

theorem toF_neg (a : Fe) (ha : a.Valid) : (Fe.neg a).toF = -a.toF := by
  rw [Fe.neg, toF_sub _ _ zero_valid ha, zero_toF]
  clear ha; grind

theorem valid_neg (a : Fe) (ha : a.Valid) : (Fe.neg a).Valid := valid_sub _ _ zero_valid ha

/-- `Point.neg` negates: it gives the point that stands for the specification's negation. -/
theorem rep_neg {p : Point} {a : Spec.Point} (hp : Rep p a) : Rep (Point.neg p) (Spec.neg a) := by
  obtain ⟨px, py, pz, rp⟩ := hp
  refine ⟨px, valid_neg _ py, pz, ?_⟩
  show RepF p.x.toF (Fe.neg p.y).toF p.z.toF (Spec.neg a)
  rw [toF_neg _ py]
  clear px py pz
  match a, rp with
  | .inf, ⟨hx, hz, hy⟩ => exact ⟨hx, hz, fun e => hy (by grind)⟩
  | .pt x y, ⟨w, hw, hx, hy⟩ => exact ⟨w, hw, hx, by simp only [hy]; grind⟩

/-! ## From three coordinates to two -/

/-- `inv` gives the inverse: an element that is not zero, times its `inv`, is one. -/
theorem inv_mul (a : Fe) (h : a.toF ≠ 0) : a.toF * (Fe.inv a).toF = 1 := by
  apply Fin.ext
  have nonzero : a.toNat % Secp.P ≠ 0 := by
    intro e
    apply h
    apply Fin.ext
    rw [Fe.toF_val, P_eq]
    exact e
  rw [Fin.val_mul, Fe.toF_val, Fe.toF_val, inv_spec, P_eq, Nat.mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]
  exact Secp.Primes.power_inverse_P a.toNat nonzero

theorem valid_inv (a : Fe) : (Fe.inv a).Valid := by
  rw [Fe.Valid, inv_spec]
  exact Nat.mod_lt _ (by decide)

/-- From three coordinates to two: for a point that is not the point at infinity, `affine` gives its x and y
and says so. -/
theorem affine_point {p : Point} {x y : F} (h : Rep p (.pt x y)) :
    p.affine.1.toF = x ∧ p.affine.2.1.toF = y ∧ p.affine.2.2 = 0 ∧ p.affine.1.Valid ∧ p.affine.2.1.Valid := by
  obtain ⟨_, _, vz, w, hw, hx, hy⟩ := h
  have hz : p.z.toF ≠ 0 := ne_zero_of_mul_eq_one hw
  have hi := inv_mul p.z hz
  have same : w = (Fe.inv p.z).toF := by
    generalize (Fe.inv p.z).toF = i at hi ⊢
    clear hz vz
    grind
  refine ⟨?_, ?_, ?_, valid_mul _ _, valid_mul _ _⟩
  · simp only [Point.affine, toF_mul]
    rw [hx, same]
  · simp only [Point.affine, toF_mul]
    rw [hy, same]
  · simp only [Point.affine, Fe.isZero_spec]
    have : p.z.toNat ≠ 0 := by
      intro e
      apply hz
      rw [Fe.toF, e]
      rfl
    simp only [this, ↓reduceIte]

/-- And for the point at infinity it says that. -/
theorem affine_infinity {p : Point} (h : Rep p .inf) : p.affine.2.2 = 1 := by
  obtain ⟨_, _, vz, _, hz, _⟩ := h
  have zero : p.z.toNat = 0 := by
    have val := congrArg Fin.val hz
    rw [Fe.toF_val, Nat.mod_eq_of_lt vz] at val
    exact val
  simp only [Point.affine, Fe.isZero_spec, zero, ↓reduceIte]

/-- The public point of a scalar: the two coordinates the code computes for `k` are those of `k · G` in the
specification, whenever that is a point and not the point at infinity. -/
theorem public_point (k : Sc) {x y : F} (h : Spec.smul k.toNat Spec.G = .pt x y) :
    (Point.mulGenerator k).affine.1.toF = x ∧ (Point.mulGenerator k).affine.2.1.toF = y
      ∧ (Point.mulGenerator k).affine.2.2 = 0 := by
  have rep := mulGenerator_rep k
  rw [h] at rep
  obtain ⟨hx, hy, flag, _, _⟩ := affine_point rep
  exact ⟨hx, hy, flag⟩

/-- From three coordinates back to the specification: what a point stands for can be read off what `affine`
returns. Either it says the point at infinity, and that is what the point stands for; or it gives two
coordinates below P, and the point stands for the point they name. -/
theorem affine_spec {p : Point} {c : Spec.Point} (h : Rep p c) :
    (p.affine.2.2 = 1 ∧ c = .inf)
    ∨ (p.affine.2.2 = 0 ∧ c = .pt p.affine.1.toF p.affine.2.1.toF ∧ p.affine.1.Valid ∧ p.affine.2.1.Valid) := by
  cases c with
  | inf => exact Or.inl ⟨affine_infinity h, rfl⟩
  | pt x y =>
    obtain ⟨hx, hy, flag, vx, vy⟩ := affine_point h
    exact Or.inr ⟨flag, by rw [hx, hy], vx, vy⟩

end SecpCt
