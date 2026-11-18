import SecpCt.Proofs
import SecpCt.Scalar

/-! # What is proved about the scalars

The same ladder as for the field (`SecpCt/Proofs.lean`), for numbers modulo N: comparing with N, the one
reduction every operation ends in, addition and negation. Each gives the right number modulo N and a result
below N.

Multiplication is in `SecpCt/ScalarMulProofs.lean`.

Nothing that runs imports this file; `SecpCt/Gate.lean` does. -/

namespace SecpCt

def Sc.toNat (a : Sc) : Nat := value a.a0 a.a1 a.a2 a.a3

/-- N, the number of points on the curve. -/
def N : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- The four words the code holds N in are N. -/
theorem n_words : value Sc.n0 Sc.n1 Sc.n2 Sc.n3 = N := by decide

/-- `lessN` takes N away, borrowing 2²⁵⁶ when it has to; the borrow is 0 or 1. -/
theorem lessN_spec (u0 u1 u2 u3 : UInt64) :
    (Sc.lessN u0 u1 u2 u3).1.toNat + N = value u0 u1 u2 u3 + (Sc.lessN u0 u1 u2 u3).2.toNat * 2 ^ 256
    ∧ (Sc.lessN u0 u1 u2 u3).2.toNat ≤ 1 := by
  have h := sbb4_spec u0 u1 u2 u3 Sc.n0 Sc.n1 Sc.n2 Sc.n3
  rw [n_words] at h
  exact h

/-- What four words stand for, as a scalar, is below 2²⁵⁶. -/
theorem Sc.toNat_lt (a : Sc) : a.toNat < 2 ^ 256 := value_lt a.a0 a.a1 a.a2 a.a3

/-- `lessN` says "below N" exactly when the number is below N. -/
theorem lessN_below (u0 u1 u2 u3 : UInt64) :
    (Sc.lessN u0 u1 u2 u3).2.toNat = if value u0 u1 u2 u3 < N then 1 else 0 := by
  obtain ⟨e, hb⟩ := lessN_spec u0 u1 u2 u3
  have ht := (Sc.lessN u0 u1 u2 u3).1.toNat_lt
  generalize (Sc.lessN u0 u1 u2 u3).1.toNat = t at *
  generalize (Sc.lessN u0 u1 u2 u3).2.toNat = b at *
  generalize value u0 u1 u2 u3 = v at *
  simp only [N, Nat.reducePow] at *
  by_cases hv : v < 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 <;>
    simp only [hv, ↓reduceIte] <;> omega

/-- `reduceOnce` gives a number below 2N modulo N: N is taken away exactly when the number is N or more. -/
theorem reduceOnce_spec (u0 u1 u2 u3 k : UInt64) (hk : k.toNat ≤ 1)
    (small : value u0 u1 u2 u3 + k.toNat * 2 ^ 256 < 2 * N) :
    (Sc.reduceOnce u0 u1 u2 u3 k).toNat = (value u0 u1 u2 u3 + k.toNat * 2 ^ 256) % N := by
  obtain ⟨e, hb⟩ := lessN_spec u0 u1 u2 u3
  have ht := (Sc.lessN u0 u1 u2 u3).1.toNat_lt
  simp only [Sc.reduceOnce, Sc.toNat] at *
  generalize (Sc.lessN u0 u1 u2 u3).1 = t at *
  generalize (Sc.lessN u0 u1 u2 u3).2 = below at *
  rcases bit_cases k hk with rfl | rfl <;> rcases bit_cases below hb with rfl | rfl
  all_goals
    (first
      | rw [show mask ((0 : UInt64) ||| ((0 : UInt64) ^^^ 1)) = mask 1 from rfl]
      | rw [show mask ((0 : UInt64) ||| ((1 : UInt64) ^^^ 1)) = mask 0 from rfl]
      | rw [show mask ((1 : UInt64) ||| ((0 : UInt64) ^^^ 1)) = mask 1 from rfl]
      | rw [show mask ((1 : UInt64) ||| ((1 : UInt64) ^^^ 1)) = mask 1 from rfl])
    (first
      | rw [select_zero, select_zero, select_zero, select_zero]
      | rw [select_one, select_one, select_one, select_one])
    simp only [show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl] at *
    generalize value t.a0 t.a1 t.a2 t.a3 = T at *
    generalize value u0 u1 u2 u3 = v at *
    simp only [N, Nat.reducePow, Nat.reduceMul] at *
  · -- no carry, not below N: N comes off
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · -- no carry, below N: nothing to do
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · -- a carry, and the words alone are not below N: cannot be, the whole is below 2N
    omega
  · -- a carry: N comes off, across the carry
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- What `reduceOnce` returns is below N. -/
theorem reduceOnce_lt (u0 u1 u2 u3 k : UInt64) (hk : k.toNat ≤ 1)
    (small : value u0 u1 u2 u3 + k.toNat * 2 ^ 256 < 2 * N) : (Sc.reduceOnce u0 u1 u2 u3 k).toNat < N := by
  rw [reduceOnce_spec u0 u1 u2 u3 k hk small]
  exact Nat.mod_lt _ (by decide)

/-- `a + b` modulo N, for two scalars below N. -/
theorem Sc.add_spec (a b : Sc) (ha : a.toNat < N) (hb : b.toNat < N) :
    (Sc.add a b).toNat = (a.toNat + b.toNat) % N := by
  obtain ⟨e, hk⟩ := adc4_spec a.a0 a.a1 a.a2 a.a3 b.a0 b.a1 b.a2 b.a3
  simp only [Sc.add, Sc.toNat] at *
  generalize (adc a.a0 b.a0 0).1 = s0 at *
  generalize (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).1 = s1 at *
  generalize (adc a.a2 b.a2 (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).2).1 = s2 at *
  generalize (adc a.a3 b.a3 (adc a.a2 b.a2 (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).2).2).1 = s3 at *
  generalize (adc a.a3 b.a3 (adc a.a2 b.a2 (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).2).2).2 = k at *
  have h := reduceOnce_spec s0 s1 s2 s3 k hk (by rw [e]; omega)
  simp only [Sc.toNat] at h
  rw [h, e]

/-- The sum of two scalars below N is below N. -/
theorem Sc.add_lt (a b : Sc) (ha : a.toNat < N) (hb : b.toNat < N) : (Sc.add a b).toNat < N := by
  rw [Sc.add_spec a b ha hb]
  exact Nat.mod_lt _ (by decide)

/-- `isZero` is 1 for zero and 0 for everything else. -/
theorem Sc.isZero_spec (a : Sc) : Sc.isZero a = if a.toNat = 0 then 1 else 0 := by
  simp only [Sc.isZero, nonzero_spec, Sc.toNat]
  by_cases h : value a.a0 a.a1 a.a2 a.a3 = 0
  · simp only [h, (words_zero a.a0 a.a1 a.a2 a.a3).mpr h, ↓reduceIte]
    rfl
  · have words : ¬ (a.a0 ||| a.a1 ||| a.a2 ||| a.a3 = 0) := fun w => h ((words_zero a.a0 a.a1 a.a2 a.a3).mp w)
    simp only [h, words, ↓reduceIte]
    rfl

/-- `−a` modulo N, for a scalar below N: N − a, and zero for zero. -/
theorem Sc.neg_spec (a : Sc) (ha : a.toNat < N) : (Sc.neg a).toNat = (N - a.toNat) % N := by
  obtain ⟨e, hb⟩ := sbb4_spec Sc.n0 Sc.n1 Sc.n2 Sc.n3 a.a0 a.a1 a.a2 a.a3
  rw [n_words] at e
  have ht := value_lt (sbb Sc.n0 a.a0 0).1 (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).1
    (sbb Sc.n2 a.a2 (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).2).1
    (sbb Sc.n3 a.a3 (sbb Sc.n2 a.a2 (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).2).2).1
  simp only [Sc.neg, Sc.isZero_spec]
  simp only [Sc.toNat] at *
  generalize (sbb Sc.n0 a.a0 0).1 = t0 at *
  generalize (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).1 = t1 at *
  generalize (sbb Sc.n2 a.a2 (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).2).1 = t2 at *
  generalize (sbb Sc.n3 a.a3 (sbb Sc.n2 a.a2 (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).2).2).1 = t3 at *
  generalize (sbb Sc.n3 a.a3 (sbb Sc.n2 a.a2 (sbb Sc.n1 a.a1 (sbb Sc.n0 a.a0 0).2).2).2).2.toNat = b at *
  by_cases zero : value a.a0 a.a1 a.a2 a.a3 = 0
  · simp only [zero, ↓reduceIte]
    rw [show mask ((1 : UInt64) ^^^ 1) = mask 0 from rfl, and_mask_zero, and_mask_zero, and_mask_zero, and_mask_zero]
    rw [Nat.sub_zero, Nat.mod_self]
    rfl
  · simp only [zero, ↓reduceIte]
    rw [show mask ((0 : UInt64) ^^^ 1) = mask 1 from rfl, and_mask_one, and_mask_one, and_mask_one, and_mask_one]
    generalize value t0 t1 t2 t3 = T at *
    generalize value a.a0 a.a1 a.a2 a.a3 = A at *
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [N, Nat.reducePow] at *
    omega

/-- The negation of a scalar below N is below N. -/
theorem Sc.neg_lt (a : Sc) (ha : a.toNat < N) : (Sc.neg a).toNat < N := by
  rw [Sc.neg_spec a ha]
  exact Nat.mod_lt _ (by decide)

/-- `choose` takes the first scalar under a mask from a bit of 1, the second from a bit of 0. -/
theorem Sc.choose_one (a b : Sc) : Sc.choose (mask 1) a b = a := by
  simp only [Sc.choose, select_one]

theorem Sc.choose_zero (a b : Sc) : Sc.choose (mask 0) a b = b := by
  simp only [Sc.choose, select_zero]

/-- `negIf` negates on a bit of 1 and leaves alone on a bit of 0. -/
theorem Sc.negIf_one (a : Sc) : Sc.negIf 1 a = Sc.neg a := Sc.choose_one _ _

theorem Sc.negIf_zero (a : Sc) : Sc.negIf 0 a = a := Sc.choose_zero _ _

end SecpCt
