import Secp.Field.Limbs
import SecpCt.Word
import SecpCt.Field

/-! # What is proved about the words

The bottom of the proofs about `SecpCt`: the word operations everything else is built from mean what they
are meant to.

A carry is worked out from the top bits of the operands and of the sum, and a borrow likewise. That those
formulas give the carry and the borrow is shown from what the top bit of a word is (`carry_top`,
`borrow_top`), with nothing left to a solver: every proof here is checked by Lean's kernel. The wide product
is winnow's, operation for operation, and takes winnow's proof (`Secp/Field/Limbs.lean`).

Of the field, addition, subtraction, negation, multiplication and the final reduction are proved (`add_spec`,
`sub_spec`, `neg_spec`, `mul_spec`, `canon_spec`): each gives the right number modulo P, and a result below P.
Inversion is proved to be the power P − 2 (`inv_spec`). The scalars are in `SecpCt/ScalarProofs.lean` and
`SecpCt/ScalarMulProofs.lean`, and what is proved of the curve in `SecpCt/CurveProofs.lean`.

Nothing that runs imports this file; `SecpCt/Gate.lean` does, so that it is checked with every build. -/

namespace SecpCt

/-- The top bit of a number below 2⁶⁴ is set exactly when the number is 2⁶³ or more. -/
theorem top_testBit (n : Nat) (h : n < 2 ^ 64) : n.testBit 63 = decide (n ≥ 2 ^ 63) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  apply propext
  omega

/-- The top bit of a word's complement is the opposite of the word's. -/
theorem top_not (s : UInt64) : (~~~s).toNat.testBit 63 = !s.toNat.testBit 63 := by
  have lt := s.toNat_lt
  rw [UInt64.toNat_not, show UInt64.size - 1 - s.toNat = 2 ^ 64 - (s.toNat + 1) by simp only [UInt64.size]; omega,
    Nat.testBit_two_pow_sub_succ lt]
  simp

/-- The top bit of a word, taken by shifting, as a number: 1 if the word is 2⁶³ or more. -/
theorem top_bit (x : UInt64) : (x >>> 63).toNat = if x.toNat ≥ 2 ^ 63 then 1 else 0 := by
  have lt := x.toNat_lt
  rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from rfl, Nat.shiftRight_eq_div_pow]
  by_cases h : x.toNat ≥ 2 ^ 63 <;> simp only [h, ↓reduceIte] <;> omega

/-- The carry formula's top bit: both top bits set, or one of them and not the sum's. -/
theorem carry_top (a b s : UInt64) :
    ((a &&& b) ||| ((a ||| b) &&& ~~~s)).toNat ≥ 2 ^ 63 ↔
      (a.toNat ≥ 2 ^ 63 ∧ b.toNat ≥ 2 ^ 63) ∨ ((a.toNat ≥ 2 ^ 63 ∨ b.toNat ≥ 2 ^ 63) ∧ s.toNat < 2 ^ 63) := by
  have e := top_testBit _ ((a &&& b) ||| ((a ||| b) &&& ~~~s)).toNat_lt
  have ha := top_testBit _ a.toNat_lt
  have hb := top_testBit _ b.toNat_lt
  have hs := top_testBit _ s.toNat_lt
  have key : ((a &&& b) ||| ((a ||| b) &&& ~~~s)).toNat ≥ 2 ^ 63
      ↔ ((a &&& b) ||| ((a ||| b) &&& ~~~s)).toNat.testBit 63 = true := by
    rw [e, decide_eq_true_eq]
  rw [key]
  clear key e
  simp only [UInt64.toNat_or, UInt64.toNat_and, Nat.testBit_or, Nat.testBit_and, top_not, ha, hb, hs]
  by_cases A : a.toNat ≥ 2 ^ 63 <;> by_cases B : b.toNat ≥ 2 ^ 63 <;> by_cases C : s.toNat ≥ 2 ^ 63 <;>
    simp [A, B, C] <;> omega

/-- `a + b + k` is the sum plus 2⁶⁴ times the carry, and the carry is 0 or 1. -/
theorem adc_toNat (a b k : UInt64) (hk : k.toNat ≤ 1) :
    (adc a b k).1.toNat + (adc a b k).2.toNat * 2 ^ 64 = a.toNat + b.toNat + k.toNat ∧ (adc a b k).2.toNat ≤ 1 := by
  have la := a.toNat_lt; have lb := b.toNat_lt
  have top := carry_top a b (a + b + k)
  simp only [adc, carryOf, top_bit]
  have sum : (a + b + k).toNat = (a.toNat + b.toNat + k.toNat) % 2 ^ 64 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, Nat.mod_add_mod]
  rw [sum] at top ⊢
  generalize ((a &&& b) ||| ((a ||| b) &&& ~~~(a + b + k))).toNat = e at *
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  generalize k.toNat = K at *
  by_cases c : e ≥ 2 ^ 63 <;> simp only [c, ↓reduceIte] <;> omega

/-- The same, with the carry in bounded as a word. -/
theorem adc_spec (a b k : UInt64) (hk : k ≤ 1) :
    (adc a b k).1.toNat + (adc a b k).2.toNat * 2 ^ 64 = a.toNat + b.toNat + k.toNat ∧ (adc a b k).2.toNat ≤ 1 :=
  adc_toNat a b k (by simpa [UInt64.le_iff_toNat_le] using hk)

/-- The borrow formula's top bit: `a`'s top bit clear and `b`'s set, or one of those and the difference's set. -/
theorem borrow_top (a b d : UInt64) :
    ((~~~a &&& b) ||| ((~~~a ||| b) &&& d)).toNat ≥ 2 ^ 63 ↔
      (a.toNat < 2 ^ 63 ∧ b.toNat ≥ 2 ^ 63) ∨ ((a.toNat < 2 ^ 63 ∨ b.toNat ≥ 2 ^ 63) ∧ d.toNat ≥ 2 ^ 63) := by
  have e := top_testBit _ ((~~~a &&& b) ||| ((~~~a ||| b) &&& d)).toNat_lt
  have ha := top_testBit _ a.toNat_lt
  have hb := top_testBit _ b.toNat_lt
  have hd := top_testBit _ d.toNat_lt
  have key : ((~~~a &&& b) ||| ((~~~a ||| b) &&& d)).toNat ≥ 2 ^ 63
      ↔ ((~~~a &&& b) ||| ((~~~a ||| b) &&& d)).toNat.testBit 63 = true := by
    rw [e, decide_eq_true_eq]
  rw [key]
  clear key e
  simp only [UInt64.toNat_or, UInt64.toNat_and, Nat.testBit_or, Nat.testBit_and, top_not, ha, hb, hd]
  by_cases A : a.toNat ≥ 2 ^ 63 <;> by_cases B : b.toNat ≥ 2 ^ 63 <;> by_cases C : d.toNat ≥ 2 ^ 63 <;>
    simp [A, B, C] <;> omega

/-- `a − b − k` is the difference less 2⁶⁴ times the borrow, and the borrow is 0 or 1. -/
theorem sbb_toNat (a b k : UInt64) (hk : k.toNat ≤ 1) :
    (sbb a b k).1.toNat + b.toNat + k.toNat = a.toNat + (sbb a b k).2.toNat * 2 ^ 64 ∧ (sbb a b k).2.toNat ≤ 1 := by
  have la := a.toNat_lt; have lb := b.toNat_lt
  have top := borrow_top a b (a - b - k)
  simp only [sbb, borrowOf, top_bit]
  have difference : (a - b - k).toNat = (2 ^ 64 - k.toNat + (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64) % 2 ^ 64 := by
    rw [UInt64.toNat_sub, UInt64.toNat_sub]
  rw [difference] at top ⊢
  generalize ((~~~a &&& b) ||| ((~~~a ||| b) &&& (a - b - k))).toNat = e at *
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  generalize k.toNat = K at *
  by_cases c : e ≥ 2 ^ 63 <;> simp only [c, ↓reduceIte] <;> omega

/-- The same, with the borrow in bounded as a word. -/
theorem sbb_spec (a b k : UInt64) (hk : k ≤ 1) :
    (sbb a b k).1.toNat + b.toNat + k.toNat = a.toNat + (sbb a b k).2.toNat * 2 ^ 64 ∧ (sbb a b k).2.toNat ≤ 1 :=
  sbb_toNat a b k (by simpa [UInt64.le_iff_toNat_le] using hk)

/-- The wide product is winnow's, operation for operation. -/
theorem mulWide_eq (a b : UInt64) : mulWide a b = Secp.mulWide a b := rfl

/-- The two words of `mulWide` are the product. -/
theorem mulWide_spec (a b : UInt64) : (mulWide a b).1.toNat * 2 ^ 64 + (mulWide a b).2.toNat = a.toNat * b.toNat := by
  rw [mulWide_eq]
  exact Secp.mulWide_spec a b

/-- `a · b + c + d` is exactly the two words `mulAdd` returns: nothing is lost to a carry. This is the step
every multi-word product and reduction in `SecpCt` is a chain of. -/
theorem mulAdd_spec (a b c d : UInt64) :
    (mulAdd a b c d).1.toNat * 2 ^ 64 + (mulAdd a b c d).2.toNat = a.toNat * b.toNat + c.toNat + d.toNat := by
  have hw := mulWide_spec a b
  obtain ⟨e1, hk1⟩ := adc_spec (mulWide a b).2 c 0 (by decide)
  obtain ⟨e2, hk2⟩ := adc_spec (adc (mulWide a b).2 c 0).1 d 0 (by decide)
  have hab : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := a.toNat_lt; omega) (by have := b.toNat_lt; omega)
  have hl2 := (adc (adc (mulWide a b).2 c 0).1 d 0).1.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [mulAdd, UInt64.toNat_add]
  simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero] at e1 e2
  generalize (adc (adc (mulWide a b).2 c 0).1 d 0).1.toNat = l2 at *
  generalize (adc (adc (mulWide a b).2 c 0).1 d 0).2.toNat = k2 at *
  generalize (adc (mulWide a b).2 c 0).1.toNat = l1 at *
  generalize (adc (mulWide a b).2 c 0).2.toNat = k1 at *
  generalize (mulWide a b).1.toNat = h at *
  generalize (mulWide a b).2.toNat = l at *
  generalize a.toNat * b.toNat = ab at *
  -- The high word and the two carries together still fit in a word, because the whole value does.
  have small : h + k1 + k2 < 2 ^ 64 := by
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub] at *
    omega
  rw [Nat.mod_eq_of_lt (by omega : h + k1 < 2 ^ 64), Nat.mod_eq_of_lt small, Nat.add_mul, Nat.add_mul]
  have step1 : h * 2 ^ 64 + k1 * 2 ^ 64 + k2 * 2 ^ 64 + l2 = h * 2 ^ 64 + k1 * 2 ^ 64 + (l2 + k2 * 2 ^ 64) := by
    simp only [Nat.add_assoc, Nat.add_comm]
  rw [step1, e2]
  have step2 : h * 2 ^ 64 + k1 * 2 ^ 64 + (l1 + d.toNat) = h * 2 ^ 64 + (l1 + k1 * 2 ^ 64) + d.toNat := by
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [step2, e1, ← hw]
  simp only [Nat.add_assoc]

/-- The mask from a bit of 1 is all ones, from a bit of 0 all zeros. -/
theorem mask_one : mask 1 = -1 := by decide
theorem mask_zero : mask 0 = 0 := rfl

/-- A mask from a bit of 1 chooses the first word, from a bit of 0 the second. -/
theorem select_one (a b : UInt64) : select (mask 1) a b = a := by
  simp [select, mask_one]

theorem select_zero (a b : UInt64) : select (mask 0) a b = b := by
  simp [select, mask_zero]

/-- Under a mask from a bit of 1 a word is kept, from a bit of 0 it is cleared. -/
theorem and_mask_one (x : UInt64) : x &&& mask 1 = x := by
  simp [mask_one]

theorem and_mask_zero (x : UInt64) : x &&& mask 0 = 0 := by
  simp [mask_zero]

/-- `nonzero` is 0 for zero and 1 for everything else. -/
theorem nonzero_spec (x : UInt64) : nonzero x = if x = 0 then 0 else 1 := by
  have lx := x.toNat_lt
  have e := top_testBit _ (x ||| (0 - x)).toNat_lt
  have hx := top_testBit _ x.toNat_lt
  have hn := top_testBit _ (0 - x).toNat_lt
  have negative : (0 - x).toNat = (2 ^ 64 - x.toNat) % 2 ^ 64 := by
    rw [UInt64.toNat_sub]
    rfl
  have top : (x ||| (0 - x)).toNat ≥ 2 ^ 63 ↔ x.toNat ≠ 0 := by
    have key : (x ||| (0 - x)).toNat ≥ 2 ^ 63 ↔ (x ||| (0 - x)).toNat.testBit 63 = true := by
      rw [e, decide_eq_true_eq]
    rw [key, UInt64.toNat_or, Nat.testBit_or, hx, hn, negative]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  apply UInt64.toNat_inj.mp
  rw [nonzero, top_bit]
  by_cases zero : x = 0
  · have clear : ¬ (x ||| (0 - x)).toNat ≥ 2 ^ 63 := fun h => (top.mp h) (by rw [zero]; rfl)
    simp only [clear, ↓reduceIte]
    simp only [zero, ↓reduceIte]
    rfl
  · have : x.toNat ≠ 0 := fun h => zero (UInt64.toNat_inj.mp h)
    simp only [zero, ↓reduceIte, top.mpr this]
    rfl

/-- A word or-ed from several is zero only if each is. -/
theorem or_zero (u0 u1 u2 u3 : UInt64) (h : u0 ||| u1 ||| u2 ||| u3 = 0) : u0 = 0 ∧ u1 = 0 ∧ u2 = 0 ∧ u3 = 0 := by
  have n := congrArg UInt64.toNat h
  simp only [UInt64.toNat_or, show (0 : UInt64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at n
  have z (u : UInt64) (hu : u.toNat = 0) : u = 0 := UInt64.toNat_inj.mp hu
  exact ⟨z _ n.1.1.1, z _ n.1.1.2, z _ n.1.2, z _ n.2⟩

/-- A word and-ed with 1 is 0 or 1. -/
theorem and_one_cases (x : UInt64) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have n : (x &&& 1).toNat = x.toNat % 2 := by
    rw [UInt64.toNat_and, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h
  · left; exact UInt64.toNat_inj.mp (by rw [n, h]; rfl)
  · right; exact UInt64.toNat_inj.mp (by rw [n, h]; rfl)

/-! ## The field: the first step -/

/-- The number four words stand for, least significant first. -/
def value (u0 u1 u2 u3 : UInt64) : Nat := u0.toNat + u1.toNat * 2 ^ 64 + u2.toNat * 2 ^ 128 + u3.toNat * 2 ^ 192

def Fe.toNat (a : Fe) : Nat := value a.a0 a.a1 a.a2 a.a3

/-- P, the field's modulus. -/
def P : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- A word that is 0 or 1 as a number is the word 0 or the word 1. -/
theorem bit_cases (k : UInt64) (h : k.toNat ≤ 1) : k = 0 ∨ k = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left; exact UInt64.toNat_inj.mp h0
  · right; exact UInt64.toNat_inj.mp h1

/-- `canon` gives the one representative below P: for a value below 2²⁵⁶, P is taken away exactly when the
value is P or more. -/
theorem canon_spec (u0 u1 u2 u3 : UInt64) :
    (Fe.canon u0 u1 u2 u3).toNat = if value u0 u1 u2 u3 ≥ P then value u0 u1 u2 u3 - P else value u0 u1 u2 u3 := by
  obtain ⟨e0, h0⟩ := adc_spec u0 Fe.c 0 (by decide)
  obtain ⟨e1, h1⟩ := adc_spec u1 0 (adc u0 Fe.c 0).2 (by simpa [UInt64.le_iff_toNat_le] using h0)
  obtain ⟨e2, h2⟩ := adc_spec u2 0 (adc u1 0 (adc u0 Fe.c 0).2).2 (by simpa [UInt64.le_iff_toNat_le] using h1)
  obtain ⟨e3, h3⟩ := adc_spec u3 0 (adc u2 0 (adc u1 0 (adc u0 Fe.c 0).2).2).2 (by simpa [UInt64.le_iff_toNat_le] using h2)
  have hv0 := (adc u0 Fe.c 0).1.toNat_lt
  have hv1 := (adc u1 0 (adc u0 Fe.c 0).2).1.toNat_lt
  have hv2 := (adc u2 0 (adc u1 0 (adc u0 Fe.c 0).2).2).1.toNat_lt
  have hv3 := (adc u3 0 (adc u2 0 (adc u1 0 (adc u0 Fe.c 0).2).2).2).1.toNat_lt
  have hu0 := u0.toNat_lt; have hu1 := u1.toNat_lt; have hu2 := u2.toNat_lt; have hu3 := u3.toNat_lt
  simp only [Fe.canon, Fe.toNat]
  by_cases hge : value u0 u1 u2 u3 ≥ P <;> simp only [hge, ↓reduceIte] <;> rcases bit_cases _ h3 with hk | hk
  all_goals
    rw [hk] at e3 ⊢
    (first
      | rw [select_zero, select_zero, select_zero, select_zero]
      | rw [select_one, select_one, select_one, select_one]) <;>
    (simp only [value, P, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
      show Fe.c.toNat = 4294968273 from rfl, Nat.reducePow, Nat.reduceSub, Nat.zero_mul, Nat.add_zero, Nat.one_mul] at *
     omega)

/-! ## Addition and subtraction

Each is two chains of four word operations. The chains are first stated as facts about whole numbers, so that
what is left to show is a few lines of arithmetic on numbers, not sixteen words. -/

/-- Four words less four words, with the borrow passed along: as numbers, the difference plus what was taken
away is what there was, plus 2²⁵⁶ if it borrowed at the end. -/
theorem sbb4_spec (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    value (sbb a0 b0 0).1 (sbb a1 b1 (sbb a0 b0 0).2).1 (sbb a2 b2 (sbb a1 b1 (sbb a0 b0 0).2).2).1
        (sbb a3 b3 (sbb a2 b2 (sbb a1 b1 (sbb a0 b0 0).2).2).2).1 + value b0 b1 b2 b3
      = value a0 a1 a2 a3 + (sbb a3 b3 (sbb a2 b2 (sbb a1 b1 (sbb a0 b0 0).2).2).2).2.toNat * 2 ^ 256
    ∧ (sbb a3 b3 (sbb a2 b2 (sbb a1 b1 (sbb a0 b0 0).2).2).2).2.toNat ≤ 1 := by
  obtain ⟨e0, h0⟩ := sbb_spec a0 b0 0 (by decide)
  obtain ⟨e1, h1⟩ := sbb_spec a1 b1 (sbb a0 b0 0).2 (by simpa [UInt64.le_iff_toNat_le] using h0)
  obtain ⟨e2, h2⟩ := sbb_spec a2 b2 (sbb a1 b1 (sbb a0 b0 0).2).2 (by simpa [UInt64.le_iff_toNat_le] using h1)
  obtain ⟨e3, h3⟩ := sbb_spec a3 b3 (sbb a2 b2 (sbb a1 b1 (sbb a0 b0 0).2).2).2
    (by simpa [UInt64.le_iff_toNat_le] using h2)
  refine ⟨?_, h3⟩
  simp only [value, show (0 : UInt64).toNat = 0 from rfl, Nat.reducePow, Nat.add_zero] at *
  omega

/-- Four words are a number below 2²⁵⁶. -/
theorem value_lt (u0 u1 u2 u3 : UInt64) : value u0 u1 u2 u3 < 2 ^ 256 := by
  have h0 := u0.toNat_lt; have h1 := u1.toNat_lt; have h2 := u2.toNat_lt; have h3 := u3.toNat_lt
  simp only [value, Nat.reducePow] at *
  omega

/-- `c` under a mask made from a bit is `c` or nothing. -/
theorem c_masked (k : UInt64) (h : k.toNat ≤ 1) : value (Fe.c &&& mask k) 0 0 0 = k.toNat * 4294968273 := by
  rcases bit_cases k h with hk | hk <;> rw [hk] <;> rfl

/-- `a − b` in the field: for two elements below P, the difference modulo P. -/
theorem sub_spec (a b : Fe) (ha : a.toNat < P) (hb : b.toNat < P) :
    (Fe.sub a b).toNat = (a.toNat + P - b.toNat) % P := by
  obtain ⟨e, hk⟩ := sbb4_spec a.a0 a.a1 a.a2 a.a3 b.a0 b.a1 b.a2 b.a3
  simp only [Fe.sub, Fe.toNat] at *
  generalize (sbb a.a0 b.a0 0).1 = d0 at *
  generalize (sbb a.a1 b.a1 (sbb a.a0 b.a0 0).2).1 = d1 at *
  generalize (sbb a.a2 b.a2 (sbb a.a1 b.a1 (sbb a.a0 b.a0 0).2).2).1 = d2 at *
  generalize (sbb a.a3 b.a3 (sbb a.a2 b.a2 (sbb a.a1 b.a1 (sbb a.a0 b.a0 0).2).2).2).1 = d3 at *
  generalize (sbb a.a3 b.a3 (sbb a.a2 b.a2 (sbb a.a1 b.a1 (sbb a.a0 b.a0 0).2).2).2).2 = k at *
  obtain ⟨f, hk'⟩ := sbb4_spec d0 d1 d2 d3 (Fe.c &&& mask k) 0 0 0
  have hm := c_masked k hk
  have hd := value_lt d0 d1 d2 d3
  have hr := value_lt (sbb d0 (Fe.c &&& mask k) 0).1 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).1
    (sbb d2 0 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).2).1
    (sbb d3 0 (sbb d2 0 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).2).2).1
  generalize value (sbb d0 (Fe.c &&& mask k) 0).1 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).1
    (sbb d2 0 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).2).1
    (sbb d3 0 (sbb d2 0 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).2).2).1 = R at *
  generalize (sbb d3 0 (sbb d2 0 (sbb d1 0 (sbb d0 (Fe.c &&& mask k) 0).2).2).2).2.toNat = k' at *
  generalize value (Fe.c &&& mask k) 0 0 0 = M at *
  generalize value d0 d1 d2 d3 = D at *
  generalize value a.a0 a.a1 a.a2 a.a3 = A at *
  generalize value b.a0 b.a1 b.a2 b.a3 = B at *
  generalize k.toNat = K at *
  simp only [P, Nat.reducePow, Nat.reduceSub] at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with hK | hK <;> subst hK
  · -- No borrow: the difference is already right, and nothing more is taken away.
    have same : A + 115792089237316195423570985008687907853269984665640564039457584007908834671663 - B
        = (A - B) + 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by omega
    rw [same, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · -- A borrow: what is left is 2²⁵⁶ too much, which is P and `c` too much.
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Four words plus four words, with the carry passed along: as numbers, the sum, with 2²⁵⁶ for a carry out. -/
theorem adc4_spec (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    value (adc a0 b0 0).1 (adc a1 b1 (adc a0 b0 0).2).1 (adc a2 b2 (adc a1 b1 (adc a0 b0 0).2).2).1
        (adc a3 b3 (adc a2 b2 (adc a1 b1 (adc a0 b0 0).2).2).2).1
        + (adc a3 b3 (adc a2 b2 (adc a1 b1 (adc a0 b0 0).2).2).2).2.toNat * 2 ^ 256
      = value a0 a1 a2 a3 + value b0 b1 b2 b3
    ∧ (adc a3 b3 (adc a2 b2 (adc a1 b1 (adc a0 b0 0).2).2).2).2.toNat ≤ 1 := by
  obtain ⟨e0, h0⟩ := adc_spec a0 b0 0 (by decide)
  obtain ⟨e1, h1⟩ := adc_spec a1 b1 (adc a0 b0 0).2 (by simpa [UInt64.le_iff_toNat_le] using h0)
  obtain ⟨e2, h2⟩ := adc_spec a2 b2 (adc a1 b1 (adc a0 b0 0).2).2 (by simpa [UInt64.le_iff_toNat_le] using h1)
  obtain ⟨e3, h3⟩ := adc_spec a3 b3 (adc a2 b2 (adc a1 b1 (adc a0 b0 0).2).2).2
    (by simpa [UInt64.le_iff_toNat_le] using h2)
  refine ⟨?_, h3⟩
  simp only [value, show (0 : UInt64).toNat = 0 from rfl, Nat.reducePow, Nat.add_zero] at *
  omega

/-- `a + b` in the field: for two elements below P, the sum modulo P. -/
theorem add_spec (a b : Fe) (ha : a.toNat < P) (hb : b.toNat < P) :
    (Fe.add a b).toNat = (a.toNat + b.toNat) % P := by
  obtain ⟨e, hk⟩ := adc4_spec a.a0 a.a1 a.a2 a.a3 b.a0 b.a1 b.a2 b.a3
  simp only [Fe.add, Fe.toNat] at *
  generalize (adc a.a0 b.a0 0).1 = s0 at *
  generalize (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).1 = s1 at *
  generalize (adc a.a2 b.a2 (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).2).1 = s2 at *
  generalize (adc a.a3 b.a3 (adc a.a2 b.a2 (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).2).2).1 = s3 at *
  generalize (adc a.a3 b.a3 (adc a.a2 b.a2 (adc a.a1 b.a1 (adc a.a0 b.a0 0).2).2).2).2 = k at *
  obtain ⟨f, hk'⟩ := adc4_spec s0 s1 s2 s3 (Fe.c &&& mask k) 0 0 0
  have hm := c_masked k hk
  have hs := value_lt s0 s1 s2 s3
  have hcanon := canon_spec (adc s0 (Fe.c &&& mask k) 0).1 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).1
    (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).1
    (adc s3 0 (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).2).1
  simp only [Fe.toNat] at hcanon
  rw [hcanon]
  clear hcanon
  have ht := value_lt (adc s0 (Fe.c &&& mask k) 0).1 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).1
    (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).1
    (adc s3 0 (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).2).1
  generalize value (adc s0 (Fe.c &&& mask k) 0).1 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).1
    (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).1
    (adc s3 0 (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).2).1 = T at *
  generalize (adc s3 0 (adc s2 0 (adc s1 0 (adc s0 (Fe.c &&& mask k) 0).2).2).2).2.toNat = k' at *
  generalize value (Fe.c &&& mask k) 0 0 0 = M at *
  generalize value s0 s1 s2 s3 = S at *
  generalize value a.a0 a.a1 a.a2 a.a3 = A at *
  generalize value b.a0 b.a1 b.a2 b.a3 = B at *
  generalize k.toNat = K at *
  simp only [P, Nat.reducePow, Nat.reduceSub] at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with hK | hK <;> subst hK
  · -- No carry: the sum is below 2²⁵⁶ and `canon` does the rest.
    by_cases big : A + B ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663
    · rw [Nat.mod_eq_sub_mod big, Nat.mod_eq_of_lt (by omega)]
      by_cases hT : T ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663 <;> simp only [hT, ↓reduceIte] <;> omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      by_cases hT : T ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663 <;> simp only [hT, ↓reduceIte] <;> omega
  · -- A carry: the sum is 2²⁵⁶ more than the words say, which is `c` more modulo P.
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    by_cases hT : T ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663 <;> simp only [hT, ↓reduceIte] <;> omega

/-- The sum of two elements below P is again below P. -/
theorem add_lt (a b : Fe) (ha : a.toNat < P) (hb : b.toNat < P) : (Fe.add a b).toNat < P := by
  rw [add_spec a b ha hb]
  exact Nat.mod_lt _ (by decide)

/-- The difference of two elements below P is again below P. -/
theorem sub_lt (a b : Fe) (ha : a.toNat < P) (hb : b.toNat < P) : (Fe.sub a b).toNat < P := by
  rw [sub_spec a b ha hb]
  exact Nat.mod_lt _ (by decide)

/-! ## Multiplication

The sixteen word products are added up without losing a carry (`mulAdd_spec`, sixteen times), which gives the
whole product as eight words; `reduce` then brings eight words to the one representative below P. Neither
half asks anything of its inputs, so the product is right for any two four-word numbers, below P or not. -/

/-- `reduce` gives the eight-word number modulo P. The high half is folded in as `c` times itself, since 2²⁵⁶
is `c` modulo P; that can leave a fifth word, no bigger than `c`, which is folded in the same way; and if that
carries, what is left is so small that one more `c` cannot carry again. -/
theorem reduce_spec (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) :
    (Fe.reduce t0 t1 t2 t3 t4 t5 t6 t7).toNat = (value t0 t1 t2 t3 + value t4 t5 t6 t7 * 2 ^ 256) % P := by
  simp only [Fe.reduce]
  have e0 := mulAdd_spec t4 Fe.c t0 0
  generalize (mulAdd t4 Fe.c t0 0).1 = k0 at *
  generalize (mulAdd t4 Fe.c t0 0).2 = u0 at *
  have e1 := mulAdd_spec t5 Fe.c t1 k0
  generalize (mulAdd t5 Fe.c t1 k0).1 = k1 at *
  generalize (mulAdd t5 Fe.c t1 k0).2 = u1 at *
  have e2 := mulAdd_spec t6 Fe.c t2 k1
  generalize (mulAdd t6 Fe.c t2 k1).1 = k2 at *
  generalize (mulAdd t6 Fe.c t2 k1).2 = u2 at *
  have e3 := mulAdd_spec t7 Fe.c t3 k2
  generalize (mulAdd t7 Fe.c t3 k2).1 = u4 at *
  generalize (mulAdd t7 Fe.c t3 k2).2 = u3 at *
  have ew := mulWide_spec u4 Fe.c
  generalize (mulWide u4 Fe.c).1 = h at *
  generalize (mulWide u4 Fe.c).2 = l at *
  have hU : value u0 u1 u2 u3 + u4.toNat * 2 ^ 256 = value t4 t5 t6 t7 * 4294968273 + value t0 t1 t2 t3 := by
    simp only [value, show (0 : UInt64).toNat = 0 from rfl, show Fe.c.toNat = 4294968273 from rfl, Nat.reducePow,
      Nat.add_zero] at *
    omega
  have hL : value l h 0 0 = u4.toNat * 4294968273 := by
    simp only [value, show (0 : UInt64).toNat = 0 from rfl, show Fe.c.toNat = 4294968273 from rfl, Nat.reducePow,
      Nat.add_zero] at *
    omega
  clear e0 e1 e2 e3 ew
  obtain ⟨f, hk⟩ := adc4_spec u0 u1 u2 u3 l h 0 0
  have hu := value_lt u0 u1 u2 u3
  have hv := value_lt (adc u0 l 0).1 (adc u1 h (adc u0 l 0).2).1 (adc u2 0 (adc u1 h (adc u0 l 0).2).2).1
    (adc u3 0 (adc u2 0 (adc u1 h (adc u0 l 0).2).2).2).1
  generalize (adc u0 l 0).1 = v0 at *
  generalize (adc u1 h (adc u0 l 0).2).1 = v1 at *
  generalize (adc u2 0 (adc u1 h (adc u0 l 0).2).2).1 = v2 at *
  generalize (adc u3 0 (adc u2 0 (adc u1 h (adc u0 l 0).2).2).2).1 = v3 at *
  generalize (adc u3 0 (adc u2 0 (adc u1 h (adc u0 l 0).2).2).2).2 = k at *
  obtain ⟨g, hk'⟩ := adc4_spec v0 v1 v2 v3 (Fe.c &&& mask k) 0 0 0
  have hm := c_masked k hk
  have hcanon := canon_spec (adc v0 (Fe.c &&& mask k) 0).1 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).1
    (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).1
    (adc v3 0 (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).2).1
  simp only [Fe.toNat] at hcanon
  simp only [Fe.toNat]
  rw [hcanon]
  clear hcanon
  have hw := value_lt (adc v0 (Fe.c &&& mask k) 0).1 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).1
    (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).1
    (adc v3 0 (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).2).1
  generalize value (adc v0 (Fe.c &&& mask k) 0).1 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).1
    (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).1
    (adc v3 0 (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).2).1 = W at *
  generalize (adc v3 0 (adc v2 0 (adc v1 0 (adc v0 (Fe.c &&& mask k) 0).2).2).2).2.toNat = K' at *
  generalize value (Fe.c &&& mask k) 0 0 0 = Mk at *
  generalize value v0 v1 v2 v3 = V at *
  generalize value u0 u1 u2 u3 = U at *
  generalize value l h 0 0 = L at *
  have hlo := value_lt t0 t1 t2 t3
  have hhi := value_lt t4 t5 t6 t7
  generalize value t0 t1 t2 t3 = Lo at *
  generalize value t4 t5 t6 t7 = Hi at *
  generalize k.toNat = K at *
  generalize u4.toNat = U4 at *
  simp only [P, Nat.reducePow, Nat.reduceSub] at *
  have whole : Lo + Hi * 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = W + 115792089237316195423570985008687907853269984665640564039457584007908834671663 * (Hi + U4 + K) := by
    omega
  rw [whole, Nat.add_mul_mod_self_left]
  by_cases hW : W ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663 <;>
    simp only [hW, ↓reduceIte]
  · rw [Nat.mod_eq_sub_mod hW, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- The product of two four-word numbers, written out by words. -/
theorem product_by_words (a0 a1 a2 a3 b0 b1 b2 b3 M : Nat) :
    (a0 + a1 * M + a2 * M ^ 2 + a3 * M ^ 3) * (b0 + b1 * M + b2 * M ^ 2 + b3 * M ^ 3) =
      a0 * b0 + (a0 * b1 + a1 * b0) * M + (a0 * b2 + a1 * b1 + a2 * b0) * M ^ 2 +
      (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * M ^ 3 + (a1 * b3 + a2 * b2 + a3 * b1) * M ^ 4 +
      (a2 * b3 + a3 * b2) * M ^ 5 + a3 * b3 * M ^ 6 := by
  grind

/-- `a · b` in the field: the product modulo P, for any two elements. -/
theorem mul_spec (a b : Fe) : (Fe.mul a b).toNat = (a.toNat * b.toNat) % P := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [Fe.mul]
  rw [reduce_spec]
  congr 1
  have e00 := mulAdd_spec a0 b0 0 0
  generalize (mulAdd a0 b0 0 0).1 = k00 at *
  generalize (mulAdd a0 b0 0 0).2 = t0 at *
  have e01 := mulAdd_spec a0 b1 k00 0
  generalize (mulAdd a0 b1 k00 0).1 = k01 at *
  generalize (mulAdd a0 b1 k00 0).2 = r1 at *
  have e02 := mulAdd_spec a0 b2 k01 0
  generalize (mulAdd a0 b2 k01 0).1 = k02 at *
  generalize (mulAdd a0 b2 k01 0).2 = r2 at *
  have e03 := mulAdd_spec a0 b3 k02 0
  generalize (mulAdd a0 b3 k02 0).1 = r4 at *
  generalize (mulAdd a0 b3 k02 0).2 = r3 at *
  have e10 := mulAdd_spec a1 b0 r1 0
  generalize (mulAdd a1 b0 r1 0).1 = k10 at *
  generalize (mulAdd a1 b0 r1 0).2 = t1 at *
  have e11 := mulAdd_spec a1 b1 r2 k10
  generalize (mulAdd a1 b1 r2 k10).1 = k11 at *
  generalize (mulAdd a1 b1 r2 k10).2 = s2 at *
  have e12 := mulAdd_spec a1 b2 r3 k11
  generalize (mulAdd a1 b2 r3 k11).1 = k12 at *
  generalize (mulAdd a1 b2 r3 k11).2 = s3 at *
  have e13 := mulAdd_spec a1 b3 r4 k12
  generalize (mulAdd a1 b3 r4 k12).1 = r5 at *
  generalize (mulAdd a1 b3 r4 k12).2 = s4 at *
  have e20 := mulAdd_spec a2 b0 s2 0
  generalize (mulAdd a2 b0 s2 0).1 = k20 at *
  generalize (mulAdd a2 b0 s2 0).2 = t2 at *
  have e21 := mulAdd_spec a2 b1 s3 k20
  generalize (mulAdd a2 b1 s3 k20).1 = k21 at *
  generalize (mulAdd a2 b1 s3 k20).2 = w3 at *
  have e22 := mulAdd_spec a2 b2 s4 k21
  generalize (mulAdd a2 b2 s4 k21).1 = k22 at *
  generalize (mulAdd a2 b2 s4 k21).2 = w4 at *
  have e23 := mulAdd_spec a2 b3 r5 k22
  generalize (mulAdd a2 b3 r5 k22).1 = r6 at *
  generalize (mulAdd a2 b3 r5 k22).2 = w5 at *
  have e30 := mulAdd_spec a3 b0 w3 0
  generalize (mulAdd a3 b0 w3 0).1 = k30 at *
  generalize (mulAdd a3 b0 w3 0).2 = t3 at *
  have e31 := mulAdd_spec a3 b1 w4 k30
  generalize (mulAdd a3 b1 w4 k30).1 = k31 at *
  generalize (mulAdd a3 b1 w4 k30).2 = t4 at *
  have e32 := mulAdd_spec a3 b2 w5 k31
  generalize (mulAdd a3 b2 w5 k31).1 = k32 at *
  generalize (mulAdd a3 b2 w5 k31).2 = t5 at *
  have e33 := mulAdd_spec a3 b3 r6 k32
  generalize (mulAdd a3 b3 r6 k32).1 = t7 at *
  generalize (mulAdd a3 b3 r6 k32).2 = t6 at *
  have expand := product_by_words a0.toNat a1.toNat a2.toNat a3.toNat b0.toNat b1.toNat b2.toNat b3.toNat (2 ^ 64)
  simp only [Fe.toNat, value]
  simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.reducePow, Nat.add_zero] at *
  rw [expand]
  omega

/-- A product is below P whatever was multiplied. -/
theorem mul_lt (a b : Fe) : (Fe.mul a b).toNat < P := by
  rw [mul_spec]
  exact Nat.mod_lt _ (by decide)

/-- Squaring is multiplying by itself. -/
theorem sqr_spec (a : Fe) : (Fe.sqr a).toNat = (a.toNat * a.toNat) % P := mul_spec a a

/-- `−a` in the field, for an element below P. -/
theorem neg_spec (a : Fe) (ha : a.toNat < P) : (Fe.neg a).toNat = (P - a.toNat) % P := by
  have h := sub_spec Fe.zero a (by decide) ha
  rw [show Fe.zero.toNat = 0 from rfl, Nat.zero_add] at h
  exact h

/-- What `canon` returns is below P. -/
theorem canon_lt (u0 u1 u2 u3 : UInt64) : (Fe.canon u0 u1 u2 u3).toNat < P := by
  have h := value_lt u0 u1 u2 u3
  rw [canon_spec]
  generalize value u0 u1 u2 u3 = v at *
  simp only [P, Nat.reducePow, Nat.reduceSub] at *
  by_cases hv : v ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663 <;>
    simp only [hv, ↓reduceIte] <;> omega

/-! ## Inversion

`inv` raises to the power P − 2 by squaring once for each bit of the exponent and multiplying where the bit is
set. What is proved is that the result is that power. That the power is the inverse is Fermat's theorem and
needs P to be prime, which nothing here proves. -/

/-- What one bit of the exponent does to the running power: square, and multiply if the bit is set. -/
def powerStep (a : Fe) (word : UInt64) (s : Fe) (i : Nat) : Fe :=
  if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then s.sqr.mul a else s.sqr

/-- What the same bit does to the exponent reached so far. -/
def exponentStep (word : UInt64) (e i : Nat) : Nat :=
  if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then 2 * e + 1 else 2 * e

theorem power_loop (l : List Nat) (a : Fe) (word : UInt64) (r : Fe) :
    (forIn l r (fun i s => if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then pure (ForInStep.yield (s.sqr.mul a))
      else pure (ForInStep.yield s.sqr)) : Id Fe).run = l.foldl (powerStep a word) r := by
  have body : (fun (i : Nat) (s : Fe) => (if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then pure (ForInStep.yield (s.sqr.mul a))
      else pure (ForInStep.yield s.sqr) : Id (ForInStep Fe))) = fun i s => pure (ForInStep.yield (powerStep a word s i)) := by
    funext i s
    simp only [powerStep]
    split <;> rfl
  rw [body, List.forIn_pure_yield_eq_foldl]
  rfl

theorem power_fold (a : Fe) (e0 e1 e2 e3 : UInt64) :
    Fe.power a e0 e1 e2 e3 = (List.range' 0 64).foldl (powerStep a e0) ((List.range' 0 64).foldl (powerStep a e1)
      ((List.range' 0 64).foldl (powerStep a e2) ((List.range' 0 64).foldl (powerStep a e3) Fe.one))) := by
  simp [Fe.power, -List.foldl_cons, power_loop]

/-- Along the bits of a word, the running power keeps being `a` to the exponent reached so far. -/
theorem power_bits (l : List Nat) (a : Fe) (word : UInt64) (r : Fe) (e : Nat) (h : r.toNat = a.toNat ^ e % P) :
    (l.foldl (powerStep a word) r).toNat = a.toNat ^ (l.foldl (exponentStep word) e) % P := by
  induction l generalizing r e with
  | nil => exact h
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    have squared : r.sqr.toNat = a.toNat ^ (2 * e) % P := by
      rw [sqr_spec, h, ← Nat.mul_mod, ← Nat.pow_add, Nat.two_mul]
    simp only [powerStep, exponentStep]
    split
    · rw [mul_spec, squared, Nat.mod_mul_mod, Nat.pow_succ]
    · exact squared

/-- `power` is `a` to the exponent its four words spell, modulo P. -/
theorem power_spec (a : Fe) (e0 e1 e2 e3 : UInt64) :
    (Fe.power a e0 e1 e2 e3).toNat = a.toNat ^ ((List.range' 0 64).foldl (exponentStep e0)
      ((List.range' 0 64).foldl (exponentStep e1) ((List.range' 0 64).foldl (exponentStep e2)
        ((List.range' 0 64).foldl (exponentStep e3) 0)))) % P := by
  rw [power_fold]
  exact power_bits _ a e0 _ _ (power_bits _ a e1 _ _ (power_bits _ a e2 _ _ (power_bits _ a e3 _ 0 (by rw [Nat.pow_zero]; rfl))))

/-- The four words `inv` raises to spell P − 2. -/
theorem inv_exponent :
    (List.range' 0 64).foldl (exponentStep 0xFFFFFFFEFFFFFC2D) ((List.range' 0 64).foldl
      (exponentStep 0xFFFFFFFFFFFFFFFF) ((List.range' 0 64).foldl (exponentStep 0xFFFFFFFFFFFFFFFF)
        ((List.range' 0 64).foldl (exponentStep 0xFFFFFFFFFFFFFFFF) 0))) = P - 2 := by
  decide +kernel

/-- `inv` is `a` to the power P − 2, modulo P. -/
theorem inv_spec (a : Fe) : (Fe.inv a).toNat = a.toNat ^ (P - 2) % P := by
  rw [Fe.inv, power_spec, inv_exponent]

/-! ## Tests and choices -/

/-- Four words are all zero exactly when the number they stand for is. -/
theorem words_zero (u0 u1 u2 u3 : UInt64) : (u0 ||| u1 ||| u2 ||| u3 = 0) ↔ value u0 u1 u2 u3 = 0 := by
  constructor
  · intro h
    have each := or_zero u0 u1 u2 u3 h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := each
    rfl
  · intro h
    simp only [value, Nat.reducePow] at h
    have h0 : u0.toNat = 0 := by omega
    have h1 : u1.toNat = 0 := by omega
    have h2 : u2.toNat = 0 := by omega
    have h3 : u3.toNat = 0 := by omega
    have z (u : UInt64) (hu : u.toNat = 0) : u = 0 := UInt64.toNat_inj.mp hu
    rw [z u0 h0, z u1 h1, z u2 h2, z u3 h3]
    rfl

/-- `isZero` is 1 for zero and 0 for everything else. -/
theorem Fe.isZero_spec (a : Fe) : Fe.isZero a = if a.toNat = 0 then 1 else 0 := by
  simp only [Fe.isZero, nonzero_spec, Fe.toNat]
  by_cases h : value a.a0 a.a1 a.a2 a.a3 = 0
  · simp only [h, (words_zero a.a0 a.a1 a.a2 a.a3).mpr h, ↓reduceIte]
    rfl
  · have words : ¬ (a.a0 ||| a.a1 ||| a.a2 ||| a.a3 = 0) := fun w => h ((words_zero a.a0 a.a1 a.a2 a.a3).mp w)
    simp only [h, words, ↓reduceIte]
    rfl

/-- `isOdd` is the number's last bit. -/
theorem Fe.isOdd_spec (a : Fe) : (Fe.isOdd a).toNat = a.toNat % 2 := by
  simp only [Fe.isOdd, Fe.toNat, value, UInt64.toNat_and, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod,
    Nat.reducePow]
  omega

/-- `choose` takes the first element under a mask from a bit of 1, the second from a bit of 0. -/
theorem Fe.choose_one (a b : Fe) : Fe.choose (mask 1) a b = a := by
  simp only [Fe.choose, select_one]

theorem Fe.choose_zero (a b : Fe) : Fe.choose (mask 0) a b = b := by
  simp only [Fe.choose, select_zero]

end SecpCt
