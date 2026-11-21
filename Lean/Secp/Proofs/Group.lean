import Secp.Proofs.Primes
import Secp.Signing

/-! # Unconditional abelian group law for `Secp.Spec.Point`

Proves without hypotheses or extra axioms that the curve points `OnCurve` form an abelian group under
`Spec.add` with identity `.inf` and inverse `Spec.neg`, and connects bit-ladder `Spec.smul` (`k < 2²⁵⁶`)
to Peano `nsmul` (`nsmul_add`, `nsmul_mul`).

All polynomial ring lemmas are stated at top level over an abstract `[Lean.Grind.CommRing R]` so `grind`
operates purely in the polynomial ring without unfolding `Fin P` modular arithmetic. -/

namespace Secp.Spec

/-! ## Generic commutative-ring lemmas (zero `Fin P` unfolding) -/

section RingLemmas
variable {R : Type} [Lean.Grind.CommRing R]

private theorem r_zero_mul (w : R) : 0 * w = 0 := by grind
private theorem r_inv_unique {a u w : R} (h1 : a * w = 1) (h2 : a * u = 1) : u = w := by grind
private theorem r_neg_sq {y c : R} (h : y * y = c) : (-y) * (-y) = c := by grind
private theorem r_neg_neg (y : R) : - -y = y := by grind

private theorem r_tangent_curve {b x y w : R} (h : y * y = x * x * x + b) (hw : 2 * y * w = 1) :
    (3 * x * x * w * (x - (3 * x * x * w * (3 * x * x * w) - 2 * x)) - y) *
      (3 * x * x * w * (x - (3 * x * x * w * (3 * x * x * w) - 2 * x)) - y) =
      (3 * x * x * w * (3 * x * x * w) - 2 * x) * (3 * x * x * w * (3 * x * x * w) - 2 * x) *
        (3 * x * x * w * (3 * x * x * w) - 2 * x) + b := by grind

private theorem r_chord_curve {b x1 y1 x2 y2 w : R}
    (h1 : y1 * y1 = x1 * x1 * x1 + b) (h2 : y2 * y2 = x2 * x2 * x2 + b) (hw : (x2 - x1) * w = 1) :
    ((y2 - y1) * w * (x1 - ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2)) - y1) *
      ((y2 - y1) * w * (x1 - ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2)) - y1) =
      ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2) * ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2) *
        ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2) + b := by grind

private theorem r_eq_of_sub {a b : R} (h : a - b = 0) : a = b := by grind
private theorem r_mul_sub {a x y : R} (h : a * x = a * y) : a * (x - y) = 0 := by grind
private theorem r_neg_mul_neg {a w : R} (h : a * w = 1) : (-a) * (-w) = 1 := by grind
private theorem r_sub_neg (a b : R) : a - b = -(b - a) := by grind
private theorem r_neg_eq_zero {a : R} (h : -a = 0) : a = 0 := by grind
private theorem r_neg_inj {a b : R} (h : -a = -b) : a = b := by grind
private theorem r_two_mul_neg (y : R) : 2 * -y = -(2 * y) := by grind
private theorem r_two_eq_zero_of_eq_neg {y : R} (h : y = -y) : 2 * y = 0 := by grind
private theorem r_diff_squares {y1 y2 c : R} (h1 : y1 * y1 = c) (h2 : y2 * y2 = c) :
    (y1 - y2) * (y1 + y2) = 0 := by grind
private theorem r_neg_of_add_zero {a b : R} (h : a + b = 0) : b = -a := by grind

private theorem r_chord_comm {x1 y1 x2 y2 w : R} (hw : (x2 - x1) * w = 1) :
    (y2 - y1) * w * ((y2 - y1) * w) - x1 - x2 = (y1 - y2) * -w * ((y1 - y2) * -w) - x2 - x1 ∧
    (y2 - y1) * w * (x1 - ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2)) - y1 =
      (y1 - y2) * -w * (x2 - ((y1 - y2) * -w * ((y1 - y2) * -w) - x2 - x1)) - y2 :=
  ⟨by grind, by grind⟩

private theorem r_neg_tangent (x y w : R) :
    3 * x * x * w * (3 * x * x * w) - 2 * x = 3 * x * x * -w * (3 * x * x * -w) - 2 * x ∧
    -(3 * x * x * w * (x - (3 * x * x * w * (3 * x * x * w) - 2 * x)) - y) =
      3 * x * x * -w * (x - (3 * x * x * -w * (3 * x * x * -w) - 2 * x)) - -y :=
  ⟨by grind, by grind⟩

private theorem r_neg_chord (x1 y1 x2 y2 w : R) :
    (y2 - y1) * w * ((y2 - y1) * w) - x1 - x2 = (-y2 - -y1) * w * ((-y2 - -y1) * w) - x1 - x2 ∧
    -((y2 - y1) * w * (x1 - ((y2 - y1) * w * ((y2 - y1) * w) - x1 - x2)) - y1) =
      (-y2 - -y1) * w * (x1 - ((-y2 - -y1) * w * ((-y2 - -y1) * w) - x1 - x2)) - -y1 :=
  ⟨by grind, by grind⟩

private theorem r_chord_slope_quad (b x1 y1 x2 y2 w : R)
    (h1 : y1 * y1 = x1 * x1 * x1 + b) (h2 : y2 * y2 = x2 * x2 * x2 + b) (hw : (x2 - x1) * w = 1) :
    ((y2 - y1) * w) * (y1 + y2) = x1 * x1 + x1 * x2 + x2 * x2 := by grind

private theorem r_tangent_slope (x1 y1 w : R) (hw : 2 * y1 * w = 1) :
    let l := 3 * x1 * x1 * w
    (l * l - 2 * x1 = l * l - x1 - x1) ∧
    (y1 - y1 = l * (x1 - x1)) ∧
    (l * (y1 + y1) = x1 * x1 + x1 * x1 + x1 * x1) ∧
    (2 * y1 * l = 3 * x1 * x1) := by
  dsimp only; exact ⟨by grind, by grind, by grind, by grind⟩

private theorem r_chord_mul_dx (y1 y2 x1 x2 w : R) (hw : (x2 - x1) * w = 1) :
    y2 - y1 = (y2 - y1) * w * (x2 - x1) := by grind

private theorem r_cancel_2y {x1 x4 y1 y4 l : R}
    (hx : x4 = x1) (hy4 : y4 = l * (x1 - x4) - -y1) (h2 : y4 = -y1) : 2 * y1 = 0 := by grind

private theorem r_cancel_hy4 {x1 x4 y1 y4 l : R}
    (hx : x1 = x4) (hy4 : y4 = l * (x1 - x4) - -y1) : y4 = y1 := by grind

private theorem r_cancel_tangent_alg (x1 y1 x2 y2 l : R)
    (hx : l * l - x1 - x2 = x1) (s1 : y2 - -y1 = l * (x2 - x1))
    (s2 : l * (-y1 + y2) = x1 * x1 + x1 * x2 + x2 * x2) :
    2 * y1 * (-l) = 3 * x1 * x1 := by grind

private theorem r_cancel_chord_alg {x1 x4 y1 y4 l l' : R}
    (hy4 : y4 = l * (x1 - x4) - -y1) (hs2 : y4 - y1 = l' * (x4 - x1)) :
    (x4 - x1) * l' = (x4 - x1) * -l := by grind

private theorem r_cancel_coords {x1 x2 x4 x5 y1 y2 y5 l : R}
    (hx4 : x4 = l * l - x1 - x2) (hs1 : y2 - -y1 = l * (x2 - x1))
    (hx5 : x5 = -l * -l - x1 - x4) (hy5 : y5 = -l * (x1 - x5) - y1) :
    x5 = x2 ∧ y5 = y2 := ⟨by grind, by grind⟩

private theorem r_line_cubic_roots (b x x1 x2 y1 y2 x4 l1 : R)
    (c2 : y2 * y2 = x2 * x2 * x2 + b) (dx1 : x4 = l1 * l1 - x1 - x2)
    (s1a : y2 - y1 = l1 * (x2 - x1)) (s1b : l1 * (y1 + y2) = x1 * x1 + x1 * x2 + x2 * x2) :
    x * x * x + b - (y2 + l1 * (x - x2)) * (y2 + l1 * (x - x2)) =
      (x - x1) * (x - x2) * (x - x4) := by
  have hb : b = y2 * y2 - x2 * x2 * x2 := by grind
  have hy1 : y1 = y2 - l1 * (x2 - x1) := by grind
  subst hb dx1 hy1
  clear c2 s1a
  grind

private theorem r_collinear_y3 {y2 y3 x2 x3 l1 : R} (h : y3 - y2 = l1 * (x3 - x2)) :
    y3 = y2 + l1 * (x3 - x2) := by grind

private theorem r_zero_of_eq_and_sub {a b c : R} (h1 : a = b) (h2 : b - a = c) : c = 0 := by grind

private theorem r_collinear_y31 {x1 x2 x3 y1 y2 y3 l1 : R}
    (hx : x3 = x1) (s1a : y2 - y1 = l1 * (x2 - x1)) (hy3 : y3 = y2 + l1 * (x3 - x2)) :
    y3 = y1 := by grind

private theorem r_collinear_y32 {x2 x3 y2 y3 l1 : R}
    (hx : x3 = x2) (hy3 : y3 = y2 + l1 * (x3 - x2)) : y3 = y2 := by grind

private theorem r_collinear_sub {x1 x2 x4 y1 y2 l1 : R}
    (hx4 : x4 = l1 * l1 - x1 - x2) (s1a : y2 - y1 = l1 * (x2 - x1))
    (s1b : l1 * (y1 + y2) = x1 * x1 + x1 * x2 + x2 * x2) (ht2 : 2 * y2 * l1 = 3 * x2 * x2) :
    (x2 - x1) * (x2 - x4) = 0 := by grind

private theorem r_collinear_y21 {x1 x2 y1 y2 l1 : R}
    (hx : x2 = x1) (s1a : y2 - y1 = l1 * (x2 - x1)) : y2 = y1 := by grind

private theorem r_collinear_y34 {x1 x2 x3 x4 y1 y2 y3 y4 l1 : R}
    (hx : x3 = x4) (hy4 : y4 = l1 * (x1 - x4) - y1)
    (s1a : y2 - y1 = l1 * (x2 - x1)) (hy3 : y3 = y2 + l1 * (x3 - x2)) :
    y3 = -y4 := by grind

private theorem r_prep_rels {x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 l1 l2 l3 l4 : R}
    (hx4 : x4 = l1 * l1 - x1 - x2) (hy4 : y4 = l1 * (x1 - x4) - y1)
    (s1a : y2 - y1 = l1 * (x2 - x1)) (s1b : l1 * (y1 + y2) = x1 * x1 + x1 * x2 + x2 * x2)
    (hx5 : x5 = l2 * l2 - x2 - x3) (hy5 : y5 = l2 * (x2 - x5) - y2)
    (s2a : y3 - y2 = l2 * (x3 - x2)) (s2b : l2 * (y2 + y3) = x2 * x2 + x2 * x3 + x3 * x3)
    (s3a : y3 - y4 = l3 * (x3 - x4)) (s4a : y5 - y1 = l4 * (x5 - x1)) :
    l1 * (2 * y2 - l1 * (x2 - x1)) = x1 * x1 + x1 * x2 + x2 * x2 ∧
    l2 * (2 * y2 + l2 * (x3 - x2)) = x2 * x2 + x2 * x3 + x3 * x3 ∧
    (y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2) = l3 * (x3 - (l1 * l1 - x1 - x2)) ∧
    (l2 * (x2 - (l2 * l2 - x2 - x3)) - y2) - (y2 - l1 * (x2 - x1)) = l4 * ((l2 * l2 - x2 - x3) - x1) ∧
    y4 = l1 * (x2 - x4) - y2 ∧
    y1 = y2 - l1 * (x2 - x1) ∧
    y3 = y2 + l2 * (x3 - x2) := by
  subst hx4 hy4 hx5 hy5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear s2a s2b s3a s4a; grind
  · clear s1a s1b s3a s4a; grind
  · clear s1b s2b s4a; grind
  · clear s1b s2a s2b s3a; grind
  · clear s1b s2a s2b s3a s4a; grind
  · clear s1b s2a s2b s3a s4a; grind
  · clear s1a s1b s2b s3a s4a; grind

private theorem magic_6var (x1 x2 x3 y2 l1 l2 : R)
    (e1 : l1 * (2 * y2 - l1 * (x2 - x1)) = x1 * x1 + x1 * x2 + x2 * x2)
    (e2 : l2 * (2 * y2 + l2 * (x3 - x2)) = x2 * x2 + x2 * x3 + x3 * x3) :
    let x4 := l1 * l1 - x1 - x2
    let x5 := l2 * l2 - x2 - x3
    let dy34 := (y2 + l2 * (x3 - x2)) - (l1 * (x2 - x4) - y2)
    let dy51 := (l2 * (x2 - x5) - y2) - (y2 - l1 * (x2 - x1))
    dy34 * (x5 - x1) - dy51 * (x3 - x4) = -(l1 - l2) * (x3 - x4) * (x5 - x1) := by
  dsimp only; grind

private theorem magic_6var_2 (x1 x2 x3 y2 l1 l2 : R)
    (e1 : l1 * (2 * y2 - l1 * (x2 - x1)) = x1 * x1 + x1 * x2 + x2 * x2)
    (e2 : l2 * (2 * y2 + l2 * (x3 - x2)) = x2 * x2 + x2 * x3 + x3 * x3) :
    let x4 := l1 * l1 - x1 - x2
    let dy34 := (y2 + l2 * (x3 - x2)) - (l1 * (x2 - x4) - y2)
    (x1 - x3) * (x3 - x4) = (l1 - l2) * (l1 * (x3 - x4) + dy34) := by
  dsimp only; grind

private theorem magic_tangent_left (x1 x2 x3 y2 l1 l2 : R)
    (hx3 : x3 = l1 * l1 - x1 - x2)
    (hy3 : (y2 + l2 * (x3 - x2)) = l1 * (x2 - x3) - y2)
    (e1 : l1 * (2 * y2 - l1 * (x2 - x1)) = x1 * x1 + x1 * x2 + x2 * x2)
    (e2 : l2 * (2 * y2 + l2 * (x3 - x2)) = x2 * x2 + x2 * x3 + x3 * x3) :
    let y4 := l1 * (x2 - x3) - y2
    let x5 := l2 * l2 - x2 - x3
    let dy51 := (l2 * (x2 - x5) - y2) - (y2 - l1 * (x2 - x1))
    (2 * y4 * l1 + 3 * x3 * x3) * (x5 - x1) = 2 * y4 * (l2 * (x5 - x1) + dy51) ∧
    2 * y4 * (x1 - x3) = (l1 - l2) * (2 * y4 * l1 + 3 * x3 * x3) := by
  dsimp only; exact ⟨by grind, by grind⟩

private theorem magic_tangent_right (x1 x2 x3 y2 l1 l2 : R)
    (hx1 : x1 = l2 * l2 - x2 - x3)
    (hy1 : (l2 * (x2 - x1) - y2) = y2 - l1 * (x2 - x1))
    (e1 : l1 * (2 * y2 - l1 * (x2 - x1)) = x1 * x1 + x1 * x2 + x2 * x2)
    (e2 : l2 * (2 * y2 + l2 * (x3 - x2)) = x2 * x2 + x2 * x3 + x3 * x3) :
    let x4 := l1 * l1 - x1 - x2
    let dy34 := (y2 + l2 * (x3 - x2)) - (l1 * (x2 - x4) - y2)
    let y1 := y2 - l1 * (x2 - x1)
    2 * y1 * (l1 * (x3 - x4) + dy34) = (2 * y1 * l2 + 3 * x1 * x1) * (x3 - x4) := by
  dsimp only; grind

private theorem magic_double_tangent (x1 x2 x3 y2 l1 l2 : R)
    (hx3 : x3 = l1 * l1 - x1 - x2)
    (hy3 : (y2 + l2 * (x3 - x2)) = l1 * (x2 - x3) - y2)
    (hx1 : x1 = l2 * l2 - x2 - x3)
    (hy1 : (l2 * (x2 - x1) - y2) = y2 - l1 * (x2 - x1))
    (e1 : l1 * (2 * y2 - l1 * (x2 - x1)) = x1 * x1 + x1 * x2 + x2 * x2)
    (e2 : l2 * (2 * y2 + l2 * (x3 - x2)) = x2 * x2 + x2 * x3 + x3 * x3) :
    let y4 := l1 * (x2 - x3) - y2
    let y1 := y2 - l1 * (x2 - x1)
    (2 * y4 * l1 + 3 * x3 * x3) * (2 * y1) = (2 * y1 * l2 + 3 * x1 * x1) * (2 * y4) := by
  dsimp only; grind

private theorem r_glue_tl_x {x1 x2 x3 y2 y4 l1 l2 l3 : R}
    (hy4 : y4 = l1 * (x2 - x3) - y2) (ht3 : 2 * y4 * l3 = 3 * x3 * x3)
    (mt2 : 2 * (l1 * (x2 - x3) - y2) * (x1 - x3) =
      (l1 - l2) * (2 * (l1 * (x2 - x3) - y2) * l1 + 3 * x3 * x3)) :
    2 * y4 * (x1 - x3) = 2 * y4 * ((l1 - l2) * (l1 + l3)) := by grind

private theorem r_glue_dt {x1 x2 x3 y1 y2 y4 l1 l2 l3 l4 : R}
    (hy4 : y4 = l1 * (x2 - x3) - y2) (hy1 : y1 = y2 - l1 * (x2 - x1))
    (ht3 : 2 * y4 * l3 = 3 * x3 * x3) (ht4 : 2 * y1 * l4 = 3 * x1 * x1)
    (mdt : (2 * (l1 * (x2 - x3) - y2) * l1 + 3 * x3 * x3) * (2 * (y2 - l1 * (x2 - x1))) =
      (2 * (y2 - l1 * (x2 - x1)) * l2 + 3 * x1 * x1) * (2 * (l1 * (x2 - x3) - y2))) :
    (2 * y4 * (2 * y1)) * (l1 + l3) = (2 * y4 * (2 * y1)) * (l2 + l4) := by
  rw [← hy4, ← hy1, ← ht3, ← ht4] at mdt
  clear hy4 hy1 ht3 ht4
  grind

private theorem r_glue_tl_c {x1 x2 x3 x5 y2 y4 l1 l2 l3 l4 : R}
    (hx5 : x5 = l2 * l2 - x2 - x3) (hy4 : y4 = l1 * (x2 - x3) - y2) (ht3 : 2 * y4 * l3 = 3 * x3 * x3)
    (e4 : (l2 * (x2 - (l2 * l2 - x2 - x3)) - y2) - (y2 - l1 * (x2 - x1)) = l4 * ((l2 * l2 - x2 - x3) - x1))
    (mt1 : (2 * (l1 * (x2 - x3) - y2) * l1 + 3 * x3 * x3) * ((l2 * l2 - x2 - x3) - x1) =
      2 * (l1 * (x2 - x3) - y2) * (l2 * ((l2 * l2 - x2 - x3) - x1) +
        ((l2 * (x2 - (l2 * l2 - x2 - x3)) - y2) - (y2 - l1 * (x2 - x1))))) :
    (2 * y4 * (x5 - x1)) * (l1 + l3) = (2 * y4 * (x5 - x1)) * (l2 + l4) := by
  rw [← hx5] at e4 mt1
  rw [← hy4] at mt1
  generalize (l2 * (x2 - x5) - y2) - (y2 - l1 * (x2 - x1)) = dy51 at e4 mt1
  clear hx5 hy4
  grind

private theorem r_glue_c_x {x1 x2 x3 x4 y2 l1 l2 l3 : R}
    (hx4 : x4 = l1 * l1 - x1 - x2)
    (e3 : (y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2) = l3 * (x3 - (l1 * l1 - x1 - x2)))
    (m2 : (x1 - x3) * (x3 - (l1 * l1 - x1 - x2)) =
      (l1 - l2) * (l1 * (x3 - (l1 * l1 - x1 - x2)) + ((y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2)))) :
    (x3 - x4) * (x1 - x3) = (x3 - x4) * ((l1 - l2) * (l1 + l3)) := by
  rw [← hx4] at e3 m2
  generalize (y2 + l2 * (x3 - x2)) - (l1 * (x2 - x4) - y2) = dy34 at e3 m2
  clear hx4
  grind

private theorem r_glue_tr {x1 x2 x3 x4 y1 y2 l1 l2 l3 l4 : R}
    (hx4 : x4 = l1 * l1 - x1 - x2) (hy1 : y1 = y2 - l1 * (x2 - x1)) (ht4 : 2 * y1 * l4 = 3 * x1 * x1)
    (e3 : (y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2) = l3 * (x3 - (l1 * l1 - x1 - x2)))
    (mtr : 2 * (y2 - l1 * (x2 - x1)) * (l1 * (x3 - (l1 * l1 - x1 - x2)) +
        ((y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2))) =
      (2 * (y2 - l1 * (x2 - x1)) * l2 + 3 * x1 * x1) * (x3 - (l1 * l1 - x1 - x2))) :
    (2 * y1 * (x3 - x4)) * (l1 + l3) = (2 * y1 * (x3 - x4)) * (l2 + l4) := by
  rw [← hx4] at e3 mtr
  rw [← hy1] at mtr
  generalize (y2 + l2 * (x3 - x2)) - (l1 * (x2 - x4) - y2) = dy34 at e3 mtr
  clear hx4 hy1
  grind

private theorem r_glue_cc {x1 x2 x3 x4 x5 y2 l1 l2 l3 l4 : R}
    (hx4 : x4 = l1 * l1 - x1 - x2) (hx5 : x5 = l2 * l2 - x2 - x3)
    (e3 : (y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2) = l3 * (x3 - (l1 * l1 - x1 - x2)))
    (e4 : (l2 * (x2 - (l2 * l2 - x2 - x3)) - y2) - (y2 - l1 * (x2 - x1)) = l4 * ((l2 * l2 - x2 - x3) - x1))
    (m1 : ((y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2)) * ((l2 * l2 - x2 - x3) - x1) -
        ((l2 * (x2 - (l2 * l2 - x2 - x3)) - y2) - (y2 - l1 * (x2 - x1))) * (x3 - (l1 * l1 - x1 - x2)) =
      -(l1 - l2) * (x3 - (l1 * l1 - x1 - x2)) * ((l2 * l2 - x2 - x3) - x1)) :
    ((x3 - x4) * (x5 - x1)) * (l1 + l3) = ((x3 - x4) * (x5 - x1)) * (l2 + l4) := by
  rw [← hx4] at e3 m1
  rw [← hx5] at e4 m1
  generalize (y2 + l2 * (x3 - x2)) - (l1 * (x2 - x4) - y2) = dy34 at e3 m1
  generalize (l2 * (x2 - x5) - y2) - (y2 - l1 * (x2 - x1)) = dy51 at e4 m1
  clear hx4 hx5
  grind

private theorem cb_coords (x1 x2 x3 y2 l1 l2 l3 l4 : R)
    (hl : l1 + l3 = l2 + l4)
    (hx13 : x1 - x3 = (l1 - l2) * (l1 + l3))
    (e3 : (y2 + l2 * (x3 - x2)) - (l1 * (x2 - (l1 * l1 - x1 - x2)) - y2) = l3 * (x3 - (l1 * l1 - x1 - x2))) :
    let x4 := l1 * l1 - x1 - x2
    let y4 := l1 * (x2 - x4) - y2
    let x5 := l2 * l2 - x2 - x3
    let y1 := y2 - l1 * (x2 - x1)
    l3 * l3 - x4 - x3 = l4 * l4 - x1 - x5 ∧
    l3 * (x4 - (l3 * l3 - x4 - x3)) - y4 = l4 * (x1 - (l4 * l4 - x1 - x5)) - y1 := by
  dsimp only; exact ⟨by grind, by grind⟩

end RingLemmas

/-! ## Field inverse and `OnCurve` preservation -/

theorem inv_unique {a w : F} (h : a * w = 1) : inv a = w := by
  have ha : a ≠ 0 := by
    intro h0; rw [h0, r_zero_mul w] at h
    exact absurd h (by decide)
  exact r_inv_unique h (mul_inv ha)

theorem cancel_left_F {a x y : F} (ha : a ≠ 0) (h : a * x = a * y) : x = y := by
  rcases mul_eq_zero (r_mul_sub h) with h0 | h0
  · exact absurd h0 ha
  · exact r_eq_of_sub h0

private theorem sub_ne_zero_of_ne {a b : F} (h : a ≠ b) : b - a ≠ 0 :=
  fun h0 => h (r_eq_of_sub h0).symm

private theorem inv_neg {a : F} (ha : a ≠ 0) : inv (-a) = -inv a :=
  inv_unique (r_neg_mul_neg (mul_inv ha))

private theorem inv_sub_swap {x1 x2 : F} (hx : x1 ≠ x2) : inv (x1 - x2) = -inv (x2 - x1) := by
  rw [r_sub_neg x1 x2]
  exact inv_neg (sub_ne_zero_of_ne hx)

theorem G_onCurve : OnCurve G := by
  show Gy * Gy = Gx * Gx * Gx + 7
  decide

theorem tangent_onCurve {x y : F} (h : y * y = x * x * x + 7) (hy : y ≠ 0) :
    OnCurve (tangent x y) := by
  simp only [tangent, OnCurve]
  exact r_tangent_curve h (mul_inv (mul_ne_zero two_ne_zero hy))

theorem chord_onCurve {x1 y1 x2 y2 : F} (h1 : y1 * y1 = x1 * x1 * x1 + 7)
    (h2 : y2 * y2 = x2 * x2 * x2 + 7) (hx : x1 ≠ x2) : OnCurve (chord x1 y1 x2 y2) := by
  simp only [chord, OnCurve]
  exact r_chord_curve h1 h2 (mul_inv (sub_ne_zero_of_ne hx))

theorem add_onCurve {p q : Point} (hp : OnCurve p) (hq : OnCurve q) : OnCurve (add p q) := by
  match p, q with
  | .inf, _ => exact hq
  | .pt _ _, .inf => exact hp
  | .pt x1 y1, .pt x2 y2 =>
    simp only [add]
    split
    · split
      · rename_i _ h; exact tangent_onCurve hp h.2
      · trivial
    · rename_i h; exact chord_onCurve hp hq h

theorem neg_onCurve {p : Point} (hp : OnCurve p) : OnCurve (neg p) := by
  cases p with
  | inf => trivial
  | pt x y =>
    simp only [neg, OnCurve] at hp ⊢
    exact r_neg_sq hp

theorem smul_onCurve (k : Nat) {p : Point} (hp : OnCurve p) : OnCurve (smul k p) := by
  unfold smul
  generalize (List.range 256).reverse = bits
  suffices ∀ r, OnCurve r → OnCurve (bits.foldl (fun r i => if k.testBit i then add (add r r) p else add r r) r) from
    this _ trivial
  induction bits with
  | nil => intro r hr; exact hr
  | cons _ is ih =>
    intro r hr
    simp only [List.foldl_cons]
    apply ih
    split
    · exact add_onCurve (add_onCurve hr hr) hp
    · exact add_onCurve hr hr

/-! ## Identity, inverse, and commutativity -/

@[simp] theorem inf_add (p : Point) : add .inf p = p := rfl

@[simp] theorem add_inf (p : Point) : add p .inf = p := by
  cases p <;> rfl

@[simp] theorem neg_inf : neg .inf = .inf := rfl

@[simp] theorem neg_neg (p : Point) : neg (neg p) = p := by
  cases p with
  | inf => rfl
  | pt x y =>
    simp only [neg, Point.pt.injEq, true_and]
    exact r_neg_neg y

theorem chord_comm (x1 y1 x2 y2 : F) (hx : x1 ≠ x2) : chord x1 y1 x2 y2 = chord x2 y2 x1 y1 := by
  have hw := mul_inv (sub_ne_zero_of_ne hx)
  rw [chord, chord, inv_sub_swap hx]
  simp only [Point.pt.injEq]
  exact r_chord_comm hw

theorem add_comm (p q : Point) : add p q = add q p := by
  match p, q with
  | .inf, .inf => rfl
  | .inf, .pt _ _ => rfl
  | .pt _ _, .inf => rfl
  | .pt x1 y1, .pt x2 y2 =>
    simp only [add]
    by_cases hx : x1 = x2
    · subst hx
      simp only [↓reduceIte]
      by_cases hy : y1 = y2
      · subst hy; rfl
      · have hy' : y2 ≠ y1 := Ne.symm hy
        simp [hy, hy']
    · have hx' : x2 ≠ x1 := Ne.symm hx
      simp only [hx, hx', ↓reduceIte]
      exact chord_comm x1 y1 x2 y2 hx

theorem eq_or_neg_of_eq_x {x y1 y2 : F} (h1 : y1 * y1 = x * x * x + 7) (h2 : y2 * y2 = x * x * x + 7) :
    y1 = y2 ∨ y2 = -y1 := by
  rcases mul_eq_zero (r_diff_squares h1 h2) with h | h
  · exact Or.inl (r_eq_of_sub h)
  · exact Or.inr (r_neg_of_add_zero h)

theorem add_neg_self {p : Point} (hp : OnCurve p) : add p (neg p) = .inf := by
  cases p with
  | inf => rfl
  | pt x y =>
    have hy : y ≠ 0 := onCurve_y_ne_zero hp
    have hny : y ≠ -y := fun he => mul_ne_zero two_ne_zero hy (r_two_eq_zero_of_eq_neg he)
    simp [add, neg, hny]

theorem neg_add_self {p : Point} (hp : OnCurve p) : add (neg p) p = .inf := by
  rw [add_comm]; exact add_neg_self hp

theorem add_eq_inf_iff {p q : Point} (hp : OnCurve p) (hq : OnCurve q) :
    add p q = .inf ↔ q = neg p := by
  match p, q with
  | .inf, .inf => simp [neg]
  | .inf, .pt _ _ => simp [neg]
  | .pt _ _, .inf => simp [neg]
  | .pt x1 y1, .pt x2 y2 =>
    simp only [add, neg]
    by_cases hx : x1 = x2
    · subst hx
      simp only [↓reduceIte, Point.pt.injEq, true_and]
      have hy1 : y1 ≠ 0 := onCurve_y_ne_zero hp
      have hny : y1 ≠ -y1 := fun he => mul_ne_zero two_ne_zero hy1 (r_two_eq_zero_of_eq_neg he)
      rcases eq_or_neg_of_eq_x hp hq with rfl | rfl
      · simp [hy1, tangent, hny]
      · simp [hny]
    · have hx' : x2 ≠ x1 := Ne.symm hx
      simp [hx, hx', chord]

theorem neg_add {p q : Point} (hp : OnCurve p) (hq : OnCurve q) :
    neg (add p q) = add (neg p) (neg q) := by
  match p, q with
  | .inf, _ => rfl
  | .pt _ _, .inf => rfl
  | .pt x1 y1, .pt x2 y2 =>
    simp only [add, neg]
    by_cases hx : x1 = x2
    · subst hx
      simp only [↓reduceIte]
      have hy1 : y1 ≠ 0 := onCurve_y_ne_zero hp
      by_cases hy : y1 = y2
      · subst hy
        have hny1 : -y1 ≠ 0 := fun h0 => hy1 (r_neg_eq_zero h0)
        simp only [hy1, hny1, ne_eq, not_false_eq_true, and_self, ↓reduceIte, tangent, Point.pt.injEq]
        rw [r_two_mul_neg y1, inv_neg (mul_ne_zero two_ne_zero hy1)]
        exact r_neg_tangent x1 y1 (inv (2 * y1))
      · have hny : -y1 ≠ -y2 := fun h0 => hy (r_neg_inj h0)
        simp [hy, hny]
    · simp only [hx, ↓reduceIte, chord, Point.pt.injEq]
      exact r_neg_chord x1 y1 x2 y2 (inv (x2 - x1))

/-! ## Unified chord-and-tangent slope and `cancel_neg_left` -/

/-- Whenever `(.pt x2 y2) ≠ neg (.pt x1 y1)` on the curve, `add` produces `.pt x4 y4` via a slope `l`
satisfying the same polynomial laws in both the chord and tangent cases. -/
theorem add_slope {x1 y1 x2 y2 : F}
    (h1 : OnCurve (.pt x1 y1)) (h2 : OnCurve (.pt x2 y2))
    (hne : Point.pt x2 y2 ≠ neg (.pt x1 y1)) :
    ∃ x4 y4 l : F,
      add (.pt x1 y1) (.pt x2 y2) = .pt x4 y4 ∧
      x4 = l * l - x1 - x2 ∧
      y4 = l * (x1 - x4) - y1 ∧
      y2 - y1 = l * (x2 - x1) ∧
      l * (y1 + y2) = x1 * x1 + x1 * x2 + x2 * x2 ∧
      (x1 = x2 → 2 * y2 * l = 3 * x2 * x2) := by
  simp only [OnCurve] at h1 h2
  by_cases hx : x1 = x2
  · subst hx
    have hy_eq : y1 = y2 := by
      rcases eq_or_neg_of_eq_x h1 h2 with h | h
      · exact h
      · exact absurd (by simp [neg, h]) hne
    subst hy_eq
    have hy1 : y1 ≠ 0 := onCurve_y_ne_zero h1
    have hw := mul_inv (mul_ne_zero two_ne_zero hy1)
    obtain ⟨ts1, ts2, ts3, ts4⟩ := r_tangent_slope x1 y1 (inv (2 * y1)) hw
    let l := 3 * x1 * x1 * inv (2 * y1)
    exact ⟨l * l - 2 * x1, l * (x1 - (l * l - 2 * x1)) - y1, l,
      by simp [add, hy1, tangent, l], ts1, rfl, ts2, ts3, fun _ => ts4⟩
  · have hw := mul_inv (sub_ne_zero_of_ne hx)
    let l := (y2 - y1) * inv (x2 - x1)
    exact ⟨l * l - x1 - x2, l * (x1 - (l * l - x1 - x2)) - y1, l,
      by simp [add, hx, chord, l], rfl, rfl,
      r_chord_mul_dx y1 y2 x1 x2 (inv (x2 - x1)) hw,
      r_chord_slope_quad 7 x1 y1 x2 y2 (inv (x2 - x1)) h1 h2 hw,
      fun h => absurd h hx⟩

theorem cancel_neg_left {p q : Point} (hp : OnCurve p) (hq : OnCurve q) :
    add p (add (neg p) q) = q := by
  match p, q with
  | .inf, _ => rfl
  | .pt _ _, .inf => exact add_neg_self hp
  | .pt x1 y1, .pt x2 y2 =>
    by_cases hqp : Point.pt x2 y2 = .pt x1 y1
    · rw [hqp, neg_add_self hp, add_inf]
    · have hne : Point.pt x2 y2 ≠ neg (neg (.pt x1 y1)) := by simpa [neg_neg] using hqp
      obtain ⟨x4, y4, l, hadd1, hx4, hy4, hs1a, hs1b, _⟩ := add_slope (neg_onCurve hp) hq hne
      dsimp only [neg] at hadd1 hx4 hy4 hs1a hs1b ⊢
      rw [hadd1]
      have h4_curve : OnCurve (.pt x4 y4) := hadd1 ▸ add_onCurve (neg_onCurve hp) hq
      have hy1 : y1 ≠ 0 := onCurve_y_ne_zero hp
      have h4_ne : Point.pt x4 y4 ≠ neg (.pt x1 y1) := by
        intro hc
        simp only [neg, Point.pt.injEq] at hc
        exact mul_ne_zero two_ne_zero hy1 (r_cancel_2y hc.1 hy4 hc.2)
      obtain ⟨x5, y5, l', hadd2, hx5, hy5, hs2a, _, htan2⟩ := add_slope hp h4_curve h4_ne
      rw [hadd2]
      have hl' : l' = -l := by
        by_cases hx14 : x1 = x4
        · have hy4_eq : y4 = y1 := r_cancel_hy4 hx14 hy4
          have ht := htan2 hx14
          rw [← hx14, hy4_eq] at ht
          have ht' := r_cancel_tangent_alg x1 y1 x2 y2 l (hx4.symm.trans hx14.symm) hs1a hs1b
          exact cancel_left_F (mul_ne_zero two_ne_zero hy1) (ht.trans ht'.symm)
        · exact cancel_left_F (sub_ne_zero_of_ne hx14) (r_cancel_chord_alg hy4 hs2a)
      subst hl'
      simp only [Point.pt.injEq]
      exact r_cancel_coords hx4 hs1a hx5 hy5

/-! ## Associativity -/

/-- **Associativity of `Spec.add` on `OnCurve` points.** -/
theorem add_assoc {p q r : Point} (hp : OnCurve p) (hq : OnCurve q) (hr : OnCurve r) :
    add (add p q) r = add p (add q r) := by
  match p, q, r with
  | .inf, _, _ => rfl
  | _, .inf, _ => rw [add_inf, inf_add]
  | _, _, .inf => rw [add_inf, add_inf]
  | .pt x1 y1, .pt x2 y2, .pt x3 y3 =>
    by_cases hqp : Point.pt x2 y2 = neg (.pt x1 y1)
    · rw [hqp, add_neg_self hp, inf_add]
      exact (cancel_neg_left hp hr).symm
    by_cases hrq : Point.pt x3 y3 = neg (.pt x2 y2)
    · rw [hrq, add_neg_self hq, add_inf,
          add_comm (add (.pt x1 y1) (.pt x2 y2)) (neg (.pt x2 y2)),
          add_comm (.pt x1 y1) (.pt x2 y2)]
      simpa only [neg_neg] using cancel_neg_left (neg_onCurve hq) hp
    have hpq_c : OnCurve (add (.pt x1 y1) (.pt x2 y2)) := add_onCurve hp hq
    have hqr_c : OnCurve (add (.pt x2 y2) (.pt x3 y3)) := add_onCurve hq hr
    by_cases hr_pq : Point.pt x3 y3 = neg (add (.pt x1 y1) (.pt x2 y2))
    · have hlhs : add (add (.pt x1 y1) (.pt x2 y2)) (.pt x3 y3) = .inf := by
        rw [hr_pq, add_neg_self hpq_c]
      have hqr_eq : add (.pt x2 y2) (.pt x3 y3) = neg (.pt x1 y1) := by
        rw [hr_pq, add_comm (.pt x1 y1) (.pt x2 y2), neg_add hq hp]
        exact cancel_neg_left hq (neg_onCurve hp)
      rw [hlhs, hqr_eq, add_neg_self hp]
    by_cases hp_qr : add (.pt x2 y2) (.pt x3 y3) = neg (.pt x1 y1)
    · have hrhs : add (.pt x1 y1) (add (.pt x2 y2) (.pt x3 y3)) = .inf := by
        rw [hp_qr, add_neg_self hp]
      have hpq_eq : add (.pt x1 y1) (.pt x2 y2) = neg (.pt x3 y3) := by
        have hp_eq : Point.pt x1 y1 = neg (add (.pt x2 y2) (.pt x3 y3)) := by
          rw [hp_qr, neg_neg]
        rw [hp_eq, add_comm _ (.pt x2 y2), neg_add hq hr]
        exact cancel_neg_left hq (neg_onCurve hr)
      rw [hrhs, hpq_eq, neg_add_self hr]
    obtain ⟨x4, y4, l1, hpq, hx4, hy4, s1a, s1b, _⟩ := add_slope hp hq hqp
    obtain ⟨x5, y5, l2, hqr, hx5, hy5, s2a, s2b, htan2⟩ := add_slope hq hr hrq
    rw [hpq] at hr_pq hpq_c ⊢
    rw [hqr] at hp_qr hqr_c ⊢
    obtain ⟨x6, y6, l3, hlhs, hx6, hy6, s3a, _, htan3⟩ := add_slope hpq_c hr hr_pq
    obtain ⟨x6', y6', l4, hrhs, hx6', hy6', s4a, _, htan4⟩ := add_slope hp hqr_c hp_qr
    rw [hlhs, hrhs]
    by_cases hll : l1 = l2
    · subst hll
      have hy3_line : y3 = y2 + l1 * (x3 - x2) := r_collinear_y3 s2a
      have hroots := r_line_cubic_roots 7 x3 x1 x2 y1 y2 x4 l1 hq hx4 s1a s1b
      have hc3 : (y2 + l1 * (x3 - x2)) * (y2 + l1 * (x3 - x2)) = x3 * x3 * x3 + 7 := by
        rw [← hy3_line]; exact hr
      have hzero : (x3 - x1) * (x3 - x2) * (x3 - x4) = 0 := r_zero_of_eq_and_sub hc3 hroots
      rcases mul_eq_zero hzero with h12 | h34
      · rcases mul_eq_zero h12 with h31 | h32
        · have hx31 : x3 = x1 := r_eq_of_sub h31
          have hy31 : y3 = y1 := r_collinear_y31 hx31 s1a hy3_line
          rw [← hlhs, ← hrhs, ← hpq, ← hqr, hx31, hy31,
              add_comm (add (.pt x1 y1) (.pt x2 y2)) (.pt x1 y1),
              add_comm (.pt x2 y2) (.pt x1 y1)]
        · have hx32 : x3 = x2 := r_eq_of_sub h32
          have hy32 : y3 = y2 := r_collinear_y32 hx32 hy3_line
          have ht2 : 2 * y2 * l1 = 3 * x2 * x2 := by
            have := htan2 hx32.symm; rw [hy32, hx32] at this; exact this
          rcases mul_eq_zero (r_collinear_sub hx4 s1a s1b ht2) with hx21 | hx24
          · have hx21' : x2 = x1 := r_eq_of_sub hx21
            have hy21' : y2 = y1 := r_collinear_y21 hx21' s1a
            rw [← hlhs, ← hrhs, ← hpq, ← hqr, hx32, hy32, hx21', hy21']
            exact add_comm (add (.pt x1 y1) (.pt x1 y1)) (.pt x1 y1)
          · exfalso; apply hr_pq
            have hx34 : x3 = x4 := hx32.trans (r_eq_of_sub hx24)
            have hy34 : y3 = -y4 := r_collinear_y34 hx34 hy4 s1a hy3_line
            simp [neg, hx34, hy34]
      · exfalso; apply hr_pq
        have hx34 : x3 = x4 := r_eq_of_sub h34
        have hy34 : y3 = -y4 := r_collinear_y34 hx34 hy4 s1a hy3_line
        simp [neg, hx34, hy34]
    · obtain ⟨e1, e2, e3, e4, hy4_rel, hy1_rel, hy3_rel⟩ :=
        r_prep_rels hx4 hy4 s1a s1b hx5 hy5 s2a s2b s3a s4a
      have ⟨hl, hx13⟩ : l1 + l3 = l2 + l4 ∧ x1 - x3 = (l1 - l2) * (l1 + l3) := by
        by_cases hx43 : x4 = x3
        · have hy34_eq : y3 = y4 := by
            rcases eq_or_neg_of_eq_x (hx43 ▸ hpq_c) hr with h | h
            · exact h.symm
            · exact absurd (by simp [neg, hx43, h]) hr_pq
          have ht3 : 2 * y4 * l3 = 3 * x3 * x3 := by
            have := htan3 hx43; rw [hy34_eq] at this; exact this
          have hy4_nz : 2 * y4 ≠ 0 := mul_ne_zero two_ne_zero (onCurve_y_ne_zero hpq_c)
          have hhy3 : y2 + l2 * (x3 - x2) = l1 * (x2 - x3) - y2 := by
            rw [← hy3_rel, hy34_eq, hy4_rel, hx43]
          have ⟨mt1, mt2⟩ := magic_tangent_left x1 x2 x3 y2 l1 l2 (hx43.symm.trans hx4) hhy3 e1 e2
          have hx13' : x1 - x3 = (l1 - l2) * (l1 + l3) :=
            cancel_left_F hy4_nz (r_glue_tl_x (hx43 ▸ hy4_rel) ht3 mt2)
          refine ⟨?_, hx13'⟩
          by_cases hx15 : x1 = x5
          · have hy51_eq : y5 = y1 := by
              rcases eq_or_neg_of_eq_x hp (hx15 ▸ hqr_c) with h | h
              · exact h.symm
              · exact absurd (by simp [neg, ← hx15, h]) hp_qr
            have ht4 : 2 * y1 * l4 = 3 * x1 * x1 := by
              have := htan4 hx15; rw [hy51_eq, ← hx15] at this; exact this
            have hy1_nz : 2 * y1 ≠ 0 := mul_ne_zero two_ne_zero (onCurve_y_ne_zero hp)
            have hhy1 : l2 * (x2 - x1) - y2 = y2 - l1 * (x2 - x1) := by
              rw [← hy1_rel, ← hy51_eq, hy5, ← hx15]
            have mdt := magic_double_tangent x1 x2 x3 y2 l1 l2
              (hx43.symm.trans hx4) hhy3 (hx15.trans hx5) hhy1 e1 e2
            dsimp only at mdt
            exact cancel_left_F (mul_ne_zero hy4_nz hy1_nz)
              (r_glue_dt (hx43 ▸ hy4_rel) hy1_rel ht3 ht4 mdt)
          · exact cancel_left_F (mul_ne_zero hy4_nz (sub_ne_zero_of_ne hx15))
              (r_glue_tl_c hx5 (hx43 ▸ hy4_rel) ht3 e4 mt1)
        · have hd34 : x3 - x4 ≠ 0 := sub_ne_zero_of_ne hx43
          have m2 := magic_6var_2 x1 x2 x3 y2 l1 l2 e1 e2
          dsimp only at m2
          have hx13' : x1 - x3 = (l1 - l2) * (l1 + l3) :=
            cancel_left_F hd34 (r_glue_c_x hx4 e3 m2)
          refine ⟨?_, hx13'⟩
          by_cases hx15 : x1 = x5
          · have hy51_eq : y5 = y1 := by
              rcases eq_or_neg_of_eq_x hp (hx15 ▸ hqr_c) with h | h
              · exact h.symm
              · exact absurd (by simp [neg, ← hx15, h]) hp_qr
            have ht4 : 2 * y1 * l4 = 3 * x1 * x1 := by
              have := htan4 hx15; rw [hy51_eq, ← hx15] at this; exact this
            have hy1_nz : 2 * y1 ≠ 0 := mul_ne_zero two_ne_zero (onCurve_y_ne_zero hp)
            have hhy1 : l2 * (x2 - x1) - y2 = y2 - l1 * (x2 - x1) := by
              rw [← hy1_rel, ← hy51_eq, hy5, ← hx15]
            have mtr := magic_tangent_right x1 x2 x3 y2 l1 l2 (hx15.trans hx5) hhy1 e1 e2
            dsimp only at mtr
            exact cancel_left_F (mul_ne_zero hy1_nz hd34) (r_glue_tr hx4 hy1_rel ht4 e3 mtr)
          · have m1 := magic_6var x1 x2 x3 y2 l1 l2 e1 e2
            dsimp only at m1
            exact cancel_left_F (mul_ne_zero hd34 (sub_ne_zero_of_ne hx15))
              (r_glue_cc hx4 hx5 e3 e4 m1)
      obtain ⟨cx, cy⟩ := cb_coords x1 x2 x3 y2 l1 l2 l3 l4 hl hx13 e3
      simp only [Point.pt.injEq]
      rw [hy6, hy6', hx6, hx6', hy4_rel, hy1_rel, hx4, hx5]
      exact ⟨cx, cy⟩

/-! ## Scalar multiplication (`nsmul` and 256-bit `smul`) -/

/-- Mathematical scalar multiplication by Peano recursion (`0 · P = .inf`, `(n + 1) · P = n · P + P`). -/
noncomputable def nsmul : Nat → Point → Point
  | 0, _ => .inf
  | n + 1, p => add (nsmul n p) p

@[simp] theorem nsmul_zero (p : Point) : nsmul 0 p = .inf := rfl

@[simp] theorem nsmul_one (p : Point) : nsmul 1 p = p := inf_add p

@[simp] theorem nsmul_inf : ∀ n : Nat, nsmul n .inf = .inf
  | 0 => rfl
  | n + 1 => by simp [nsmul, nsmul_inf n]

theorem nsmul_onCurve : ∀ (n : Nat) {p : Point}, OnCurve p → OnCurve (nsmul n p)
  | 0, _, _ => trivial
  | n + 1, _, hp => add_onCurve (nsmul_onCurve n hp) hp

theorem nsmul_add (a : Nat) : ∀ (b : Nat) {p : Point}, OnCurve p →
    nsmul (a + b) p = add (nsmul a p) (nsmul b p)
  | 0, p, _ => by simp
  | b + 1, p, hp => by
    rw [Nat.add_succ, nsmul, nsmul, nsmul_add a b hp,
        add_assoc (nsmul_onCurve a hp) (nsmul_onCurve b hp) hp]

theorem nsmul_mul : ∀ (a b : Nat) {p : Point}, OnCurve p →
    nsmul (a * b) p = nsmul a (nsmul b p)
  | 0, _, _, _ => by simp [Nat.zero_mul]
  | a + 1, b, p, hp => by
    rw [Nat.succ_mul, nsmul_add (a * b) b hp, nsmul, nsmul_mul a b hp]

theorem nsmul_neg : ∀ (n : Nat) {p : Point}, OnCurve p →
    nsmul n (neg p) = neg (nsmul n p)
  | 0, _, _ => rfl
  | n + 1, p, hp => by
    rw [nsmul, nsmul, nsmul_neg n hp, neg_add (nsmul_onCurve n hp) hp]

private theorem smul_fold_step (k : Nat) {p : Point} (hp : OnCurve p) :
    ∀ (m : Nat),
      (List.range m).reverse.foldl (fun r i => if k.testBit i then add (add r r) p else add r r)
        (nsmul (k / 2 ^ m) p) = nsmul k p
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]
    have hbit : k.testBit m = decide (k / 2 ^ m % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    have hpow : k / 2 ^ (m + 1) = k / 2 ^ m / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    have hdiv : 2 * (k / 2 ^ (m + 1)) + k / 2 ^ m % 2 = k / 2 ^ m := by
      rw [hpow]; exact Nat.div_add_mod (k / 2 ^ m) 2
    let e := k / 2 ^ (m + 1)
    have hdouble : add (nsmul e p) (nsmul e p) = nsmul (2 * e) p := by
      rw [Nat.two_mul, nsmul_add e e hp]
    rw [hbit]
    by_cases hmod : k / 2 ^ m % 2 = 1
    · simp only [hmod, decide_true, ↓reduceIte]
      have hstep : add (add (nsmul e p) (nsmul e p)) p = nsmul (k / 2 ^ m) p := by
        rw [hdouble, ← nsmul]
        congr 1; dsimp [e]; omega
      exact hstep ▸ smul_fold_step k hp m
    · simp only [hmod, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hmod0 : k / 2 ^ m % 2 = 0 := by omega
      have hstep : add (nsmul e p) (nsmul e p) = nsmul (k / 2 ^ m) p := by
        rw [hdouble, show 2 * e = k / 2 ^ m by dsimp [e]; omega]
      exact hstep ▸ smul_fold_step k hp m

/-- For any scalar `k < 2²⁵⁶` and curve point `p`, 256-bit `Spec.smul k p` equals `nsmul k p`. -/
theorem smul_eq_nsmul (k : Nat) (hk : k < 2 ^ 256) {p : Point} (hp : OnCurve p) :
    smul k p = nsmul k p := by
  unfold smul
  have h0 : k / 2 ^ 256 = 0 := Nat.div_eq_of_lt hk
  rw [← nsmul_zero p, ← h0]
  exact smul_fold_step k hp 256

end Secp.Spec

namespace Secp.Ecdsa
open Secp.Spec (N)

private def exponentOfBits (e : Nat) (bit : Bool) : Nat := if bit then 2 * e + 1 else 2 * e

private theorem power_fold (a m : Nat) (bits : List Bool) (acc e : Nat) (h : acc = a ^ e % m) :
    bits.foldl (powerStep a m) acc = a ^ (bits.foldl exponentOfBits e) % m := by
  induction bits generalizing acc e with
  | nil => exact h
  | cons bit bits ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    have squared : acc * acc % m = a ^ (2 * e) % m := by
      rw [h, ← Nat.mul_mod, ← Nat.pow_add, Nat.two_mul]
    cases bit
    · simpa [powerStep, exponentOfBits] using squared
    · simp only [powerStep, exponentOfBits, ↓reduceIte]
      rw [squared, Nat.mod_mul_mod, Nat.pow_succ]

/-- The signer's `1/k` is `k` to the power `N − 2`, modulo `N`. -/
theorem inverse_eq (k : Nat) : inverse k = k ^ (N - 2) % N := by
  have exponent : ((List.range 256).reverse.map (fun i => (N - 2).testBit i)).foldl exponentOfBits 0
      = N - 2 := by decide +kernel
  unfold inverse
  rw [power_fold k N _ 1 0 (by rw [Nat.pow_zero]; decide), exponent]

/-- **Unconditional modular inverse mod `N`:** for any `k` not divisible by `N`, `k * inverse k % N = 1`. -/
theorem mul_inverse {k : Nat} (hk : k % N ≠ 0) : k * inverse k % N = 1 := by
  rw [inverse_eq, Nat.mul_mod_mod]
  exact Secp.Primes.power_inverse_N k hk

end Secp.Ecdsa
