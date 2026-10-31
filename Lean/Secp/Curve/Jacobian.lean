import Secp.Curve.Formulas

/-! # Jacobian arithmetic over the limb field

The implementation keeps points as `(X, Y, Z)` with `x = X/Z²`, `y = Y/Z³` and no division until
the end; `Z = 0` is the point at infinity. `Rep j a` says that `j` stands for the spec point `a`.
Doubling and mixed addition preserve `Rep` for the spec's `add` (`rep_double`, `rep_add`), so the
scalar multiplication computes `Spec.smul` (`smul?_spec`).

**Not constant-time.** `smulJ` is double-and-add over the scalar's bits, adding only where a bit is set, and
the field code underneath branches on its data and works on boxed limbs and `Nat`s, so the time a
multiplication takes depends on the (possibly secret) scalar. Correct by the proofs here, not side-channel
resistant. That is acceptable for what Winnow does with it: low-volume signing the user approves, on the
user's own device, where no one can trigger operations on demand or time them. Do not reuse it in servers,
signing services, shared hosts, or anything that signs on someone else's request (SECURITY.md, "Timing side
channels"). -/

namespace Secp
open Spec

/-- An affine point as the implementation holds it. -/
inductive APoint where
  | inf
  | pt (x y : Fq)
  deriving DecidableEq

def APoint.toSpec : APoint → Spec.Point
  | .inf => .inf
  | .pt x y => .pt x.toF y.toF

structure Jac where
  X : Fq
  Y : Fq
  Z : Fq

def Jac.inf : Jac := ⟨1, 1, 0⟩

theorem Fq.eq_zero_iff (a : Fq) : a = 0 ↔ a.toF = 0 := by
  rw [← Fq.toF_zero, Fq.toF_inj]

def Jac.double (j : Jac) : Jac :=
  if j.Z = 0 then j else
  let r := dblF j.X j.Y j.Z
  ⟨r.1, r.2.1, r.2.2⟩

def Jac.addAffine (j : Jac) (x2 y2 : Fq) : Jac :=
  if j.Z = 0 then ⟨x2, y2, 1⟩ else
  let hr := hrF j.X j.Y j.Z x2 y2
  if hr.1 = 0 then (if hr.2 = 0 then j.double else Jac.inf) else
  let r := maddF j.X j.Y j.Z x2 y2
  ⟨r.1, r.2.1, r.2.2⟩

def Jac.add (j : Jac) : APoint → Jac
  | .inf => j
  | .pt x y => j.addAffine x y

def Jac.toAffine? (j : Jac) : Option APoint :=
  if j.Z = 0 then some .inf else
  match j.Z.inv? with
  | some w => let w2 := w * w; some (.pt (j.X * w2) (j.Y * w2 * w))
  | none => none

/-- `k · p`, left-to-right over bits 255 … 0, in Jacobian form. -/
def smulJ (k : Nat) (p : APoint) : Jac :=
  (List.range 256).reverse.foldl (fun r i => if k.testBit i then r.double.add p else r.double) Jac.inf

/-- `k · p` in affine form; `none` only if the final inverse failed its check. -/
def smul? (k : Nat) (p : APoint) : Option APoint := (smulJ k p).toAffine?

/-! ## Correctness -/

/-- `j` represents the spec point `a`. -/
def Rep (j : Jac) (a : Spec.Point) : Prop :=
  (j.Z.toF = 0 ∧ a = .inf) ∨
  (j.Z.toF ≠ 0 ∧ a = .pt (j.X.toF * (inv j.Z.toF * inv j.Z.toF))
                          (j.Y.toF * (inv j.Z.toF * inv j.Z.toF * inv j.Z.toF)))

theorem rep_inf : Rep Jac.inf .inf := Or.inl ⟨by simp [Jac.inf], rfl⟩

theorem inv_unique {a w : F} (h1 : a * w = 1) (h2 : a * inv a = 1) : w = inv a := by
  calc w = w * (a * inv a) := by rw [h2]; grind
    _ = (a * w) * inv a := by grind
    _ = inv a := by rw [h1]; grind

theorem inv_one [FieldP] : inv (1 : F) = 1 := by
  have := mul_inv (a := (1 : F)) (by decide)
  grind

theorem Spec.add_inf (a : Spec.Point) : Spec.add a .inf = a := by
  cases a <;> rfl

theorem rep_double [FieldP] {j : Jac} {a : Spec.Point} (h : Rep j a) : Rep j.double (Spec.add a a) := by
  rcases h with ⟨hz, rfl⟩ | ⟨hz, rfl⟩
  · have : j.Z = 0 := (Fq.eq_zero_iff _).2 hz
    simp only [Jac.double, this, ite_true]
    exact Or.inl ⟨hz, rfl⟩
  · have hz' : j.Z ≠ 0 := fun e => hz ((Fq.eq_zero_iff _).1 e)
    have hm := dblF_map j.X j.Y j.Z
    have m1 := congrArg (·.1) hm; have m2 := congrArg (·.2.1) hm; have m3 := congrArg (·.2.2) hm
    simp only at m1 m2 m3
    rw [Jac.double, if_neg hz']
    simp only [Rep, m1, m2, m3]
    simp only [Spec.add, true_and, ite_true]
    generalize j.X.toF = X at *
    generalize j.Y.toF = Y at *
    generalize j.Z.toF = Z at *
    have hw := mul_inv hz
    generalize inv Z = w at *
    rw [dblF_Z]
    by_cases hy : Y * (w * w * w) = 0
    · have hY0 : Y = 0 := by
        have : Y = Y * (w * w * w) * (Z * Z * Z) := by grind
        rw [this, hy]; grind
      left; refine ⟨by rw [hY0]; grind, by simp [hy]⟩
    · have hY0 : Y ≠ 0 := fun e => hy (by rw [e]; grind)
      have hZ3 : 2 * Y * Z ≠ 0 := by
        intro e
        rcases mul_eq_zero e with e | e
        · rcases mul_eq_zero e with e | e
          · exact two_ne_zero e
          · exact hY0 e
        · exact hz e
      have h2y : 2 * (Y * (w * w * w)) ≠ 0 := by
        intro e; rcases mul_eq_zero e with e | e
        · exact two_ne_zero e
        · exact hy e
      have hv := mul_inv h2y
      have hw3 := mul_inv hZ3
      right
      refine ⟨hZ3, ?_⟩
      simp only [hy, not_false_eq_true, ite_true, tangent]
      have hc := dblF_correct X Y Z w _ _ hw hv (by rw [dblF_Z]; exact hw3)
      simp only at hc
      rw [hc.1, hc.2]
      exact if_pos hy

theorem rep_addAffine [FieldP] {j : Jac} {a : Spec.Point} (x2 y2 : Fq) (h : Rep j a) :
    Rep (j.addAffine x2 y2) (Spec.add a (.pt x2.toF y2.toF)) := by
  rcases h with ⟨hz, rfl⟩ | ⟨hz, rfl⟩
  · have : j.Z = 0 := (Fq.eq_zero_iff _).2 hz
    simp only [Jac.addAffine, this, ite_true]
    right
    refine ⟨by simp only [Fq.toF_one]; decide, ?_⟩
    simp only [Spec.add, Fq.toF_one, inv_one]; grind
  · have hz' : j.Z ≠ 0 := fun e => hz ((Fq.eq_zero_iff _).1 e)
    have hr := hrF_map j.X j.Y j.Z x2 y2
    have r1 := congrArg (·.1) hr; have r2 := congrArg (·.2) hr
    simp only at r1 r2
    have hw := mul_inv hz
    have ⟨e1, e2⟩ := hrF_eq j.X.toF j.Y.toF j.Z.toF x2.toF y2.toF _ hw
    have hZZ : j.Z.toF * j.Z.toF ≠ 0 := by
      intro e; rcases mul_eq_zero e with e | e <;> exact hz e
    have hZZZ : j.Z.toF * j.Z.toF * j.Z.toF ≠ 0 := by
      intro e; rcases mul_eq_zero e with e | e
      · exact hZZ e
      · exact hz e
    rw [Jac.addAffine, if_neg hz']
    by_cases hH : (hrF j.X j.Y j.Z x2 y2).1 = 0
    · have hH' := (Fq.eq_zero_iff _).1 hH
      rw [r1, e1] at hH'
      have hx : j.X.toF * (inv j.Z.toF * inv j.Z.toF) = x2.toF := by
        rcases mul_eq_zero hH' with e | e
        · grind
        · exact absurd e hZZ
      simp only [hH, ite_true]
      by_cases hR : (hrF j.X j.Y j.Z x2 y2).2 = 0
      · have hR' := (Fq.eq_zero_iff _).1 hR
        rw [r2, e2] at hR'
        have hy : j.Y.toF * (inv j.Z.toF * inv j.Z.toF * inv j.Z.toF) = y2.toF := by
          rcases mul_eq_zero hR' with e | e
          · grind
          · exact absurd e hZZZ
        simp only [hR, ite_true]
        rw [← hx, ← hy]
        exact rep_double (Or.inr ⟨hz, rfl⟩)
      · have hR' : ¬ (hrF j.X j.Y j.Z x2 y2).2.toF = 0 := fun e => hR ((Fq.eq_zero_iff _).2 e)
        rw [r2, e2] at hR'
        have hy : j.Y.toF * (inv j.Z.toF * inv j.Z.toF * inv j.Z.toF) ≠ y2.toF := by
          intro e; apply hR'; rw [e]; grind
        simp only [hR, ite_false]
        left
        refine ⟨by simp [Jac.inf], ?_⟩
        simp only [Spec.add, hx, ite_true]
        rw [if_neg (fun h => hy h.1)]
    · have hH' : ¬ (hrF j.X j.Y j.Z x2 y2).1.toF = 0 := fun e => hH ((Fq.eq_zero_iff _).2 e)
      have hd : x2.toF - j.X.toF * (inv j.Z.toF * inv j.Z.toF) ≠ 0 := by
        intro e; apply hH'; rw [r1, e1, e]; grind
      have hx : j.X.toF * (inv j.Z.toF * inv j.Z.toF) ≠ x2.toF := by
        intro e; apply hd; rw [e]; grind
      have hm := maddF_map j.X j.Y j.Z x2 y2
      have m1 := congrArg (·.1) hm; have m2 := congrArg (·.2.1) hm; have m3 := congrArg (·.2.2) hm
      simp only at m1 m2 m3
      simp only [hH, ite_false]
      have hZ3 : (maddF j.X.toF j.Y.toF j.Z.toF x2.toF y2.toF).2.2 ≠ 0 := by
        rw [maddF_Z, ← r1]
        intro e
        rcases mul_eq_zero e with e | e
        · rcases mul_eq_zero e with e | e
          · exact two_ne_zero e
          · exact hz e
        · exact hH' e
      right
      refine ⟨by rw [m3]; exact hZ3, ?_⟩
      simp only [Spec.add, hx, ite_false, chord, m1, m2, m3]
      have hv := mul_inv hd
      have hw3 := mul_inv hZ3
      have hc := maddF_correct j.X.toF j.Y.toF j.Z.toF x2.toF y2.toF _ _ _ hw hv hw3
      simp only at hc
      rw [hc.1, hc.2]

theorem rep_add [FieldP] {j : Jac} {a : Spec.Point} (p : APoint) (h : Rep j a) :
    Rep (j.add p) (Spec.add a p.toSpec) := by
  cases p with
  | inf => simp only [Jac.add, APoint.toSpec, Spec.add_inf]; exact h
  | pt x y => exact rep_addAffine x y h

theorem toAffine?_spec {j : Jac} {a : Spec.Point} {b : APoint} (h : Rep j a)
    (hb : j.toAffine? = some b) : b.toSpec = a := by
  unfold Jac.toAffine? at hb
  by_cases hz : j.Z = 0
  · simp only [hz, ite_true, Option.some.injEq] at hb
    subst hb
    rcases h with ⟨_, rfl⟩ | ⟨hz', _⟩
    · rfl
    · exact absurd ((Fq.eq_zero_iff _).1 hz) hz'
  · simp only [hz, ite_false] at hb
    have hz' : j.Z.toF ≠ 0 := fun e => hz ((Fq.eq_zero_iff _).2 e)
    rcases h with ⟨e, _⟩ | ⟨_, rfl⟩
    · exact absurd e hz'
    · split at hb
      · rename_i w hw
        simp only [Option.some.injEq] at hb
        subst hb
        have h1 := Fq.inv?_spec hw
        have h2 : j.Z.toF * inv j.Z.toF = 1 := by
          -- the checked inverse is an inverse, so `inv` takes the `then` branch
          have he : ∃ w, j.Z.toF * w = 1 := ⟨_, h1⟩
          simp only [inv, he, dite_true]
          exact Classical.choose_spec he
        have := inv_unique h1 h2
        simp only [APoint.toSpec, Fq.toF_mul, this]
        grind
      · cases hb

/-- **Scalar multiplication computes the spec.** If the implementation returns a point, it is
`Spec.smul k` of the input. -/
theorem rep_fold [FieldP] (k : Nat) (p : APoint) : ∀ (bits : List Nat) (j : Jac) (a : Spec.Point), Rep j a →
    Rep (bits.foldl (fun r i => if k.testBit i then r.double.add p else r.double) j)
        (bits.foldl (fun r i => if k.testBit i then Spec.add (Spec.add r r) p.toSpec else Spec.add r r) a)
  | [], _, _, h => h
  | i :: is, j, a, h => by
    simp only [List.foldl_cons]
    apply rep_fold k p is
    split
    · exact rep_add p (rep_double h)
    · exact rep_double h

/-- **Scalar multiplication computes the spec.** If the implementation returns a point, it is
`Spec.smul k` of the input. -/
theorem smul?_spec [FieldP] {k : Nat} {p b : APoint} (h : smul? k p = some b) :
    b.toSpec = Spec.smul k p.toSpec :=
  toAffine?_spec (rep_fold k p _ _ _ rep_inf) h

end Secp
