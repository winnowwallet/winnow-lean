import Secp.Field.Limbs

/-! # Multi-limb numbers

A number is a little-endian `List UInt64`; `val` reads it as a `Nat`. Addition, subtraction and
the multiply-accumulate row are defined by recursion over the limbs and proven once, by
induction, for every length. -/

namespace Secp

def val : List UInt64 → Nat
  | [] => 0
  | w :: ws => w.toNat + 2^64 * val ws

@[simp] theorem val_nil : val [] = 0 := rfl
@[simp] theorem val_cons (w : UInt64) (ws : List UInt64) : val (w :: ws) = w.toNat + 2^64 * val ws := rfl

theorem pow64_succ (n : Nat) : 2^(64 * (n + 1)) = 2^64 * 2^(64 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem val_lt (ws : List UInt64) : val ws < 2^(64 * ws.length) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have := w.toNat_lt
    rw [val_cons, List.length_cons, pow64_succ]
    generalize 2^(64 * ws.length) = X at *
    omega

theorem val_append (xs ys : List UInt64) : val (xs ++ ys) = val xs + 2^(64 * xs.length) * val ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, val_cons, val_cons, ih, List.length_cons, pow64_succ]
    grind

theorem val_take_drop (k : Nat) (xs : List UInt64) :
    val xs = val (xs.take k) + 2^(64 * (xs.take k).length) * val (xs.drop k) := by
  rw [← val_append, List.take_append_drop]

/-- Limb-wise addition with carry; a missing limb counts as zero. -/
def addc : List UInt64 → List UInt64 → UInt64 → List UInt64 × UInt64
  | [], [], c => ([], c)
  | a :: as, [], c => let r := adc a 0 c; let t := addc as [] r.2; (r.1 :: t.1, t.2)
  | [], b :: bs, c => let r := adc 0 b c; let t := addc [] bs r.2; (r.1 :: t.1, t.2)
  | a :: as, b :: bs, c => let r := adc a b c; let t := addc as bs r.2; (r.1 :: t.1, t.2)

theorem addc_spec : ∀ (as bs : List UInt64) (c : UInt64), c.toNat ≤ 1 →
    val (addc as bs c).1 + (addc as bs c).2.toNat * 2^(64 * (addc as bs c).1.length)
      = val as + val bs + c.toNat ∧ (addc as bs c).2.toNat ≤ 1
      ∧ (addc as bs c).1.length = max as.length bs.length
  | [], [], c, hc => by simp [addc]; omega
  | a :: as, [], c, hc => by
    have ⟨h1, h2⟩ := adc_spec a 0 c hc
    have ⟨i1, i2, i3⟩ := addc_spec as [] _ h2
    simp only [addc, val_cons, List.length_cons, val_nil] at *
    refine ⟨?_, i2, by simp [i3]⟩
    rw [pow64_succ]; simp at h1; grind
  | [], b :: bs, c, hc => by
    have ⟨h1, h2⟩ := adc_spec 0 b c hc
    have ⟨i1, i2, i3⟩ := addc_spec [] bs _ h2
    simp only [addc, val_cons, List.length_cons, val_nil] at *
    refine ⟨?_, i2, by simp [i3]⟩
    rw [pow64_succ]; simp at h1; grind
  | a :: as, b :: bs, c, hc => by
    have ⟨h1, h2⟩ := adc_spec a b c hc
    have ⟨i1, i2, i3⟩ := addc_spec as bs _ h2
    simp only [addc, val_cons, List.length_cons] at *
    refine ⟨?_, i2, by simp [i3, Nat.succ_max_succ]⟩
    rw [pow64_succ]; grind

/-- Limb-wise subtraction with borrow over equal-length lists. -/
def subb : List UInt64 → List UInt64 → UInt64 → List UInt64 × UInt64
  | a :: as, b :: bs, c => let r := sbb a b c; let t := subb as bs r.2; (r.1 :: t.1, t.2)
  | _, _, c => ([], c)

theorem subb_spec : ∀ (as bs : List UInt64) (c : UInt64), c.toNat ≤ 1 → as.length = bs.length →
    val (subb as bs c).1 + val bs + c.toNat = val as + (subb as bs c).2.toNat * 2^(64 * as.length)
      ∧ (subb as bs c).2.toNat ≤ 1 ∧ (subb as bs c).1.length = as.length
  | [], [], c, hc, _ => by simp [subb]; exact hc
  | a :: as, b :: bs, c, hc, hl => by
    have ⟨h1, h2⟩ := sbb_spec a b c hc
    have ⟨i1, i2, i3⟩ := subb_spec as bs _ h2 (by simpa using hl)
    simp only [subb, val_cons, List.length_cons] at *
    refine ⟨?_, i2, by simp [i3]⟩
    rw [pow64_succ]; grind
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl

/-- `x * bs + c`, one limb longer than `bs`. -/
def mulAddRow (x : UInt64) : List UInt64 → UInt64 → List UInt64
  | [], c => [c]
  | b :: bs, c =>
    let m := mulWide x b
    let s := adc m.2 c 0
    s.1 :: mulAddRow x bs (m.1 + s.2)

theorem mulAddRow_spec (x : UInt64) : ∀ (bs : List UInt64) (c : UInt64),
    val (mulAddRow x bs c) = x.toNat * val bs + c.toNat ∧ (mulAddRow x bs c).length = bs.length + 1
  | [], c => by simp [mulAddRow]
  | b :: bs, c => by
    have hm := mulWide_spec x b
    have hhi := mulWide_hi_le x b
    have ⟨hs, hk⟩ := adc_spec (mulWide x b).2 c 0 (by simp)
    have hcarry : ((mulWide x b).1 + (adc (mulWide x b).2 c 0).2).toNat
        = (mulWide x b).1.toNat + (adc (mulWide x b).2 c 0).2.toNat := by
      rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; omega
    have ⟨i1, i2⟩ := mulAddRow_spec x bs ((mulWide x b).1 + (adc (mulWide x b).2 c 0).2)
    simp only [mulAddRow, val_cons, List.length_cons] at *
    refine ⟨?_, by simp [i2]⟩
    rw [i1, hcarry]; simp at hs; grind

/-- The full product, `as.length + bs.length` limbs or more. -/
def mulL : List UInt64 → List UInt64 → List UInt64
  | [], _ => []
  | a :: as, bs =>
    let r := mulAddRow a bs 0
    let t := addc r (0 :: mulL as bs) 0
    t.1 ++ [t.2]

theorem mulL_spec : ∀ (as bs : List UInt64), val (mulL as bs) = val as * val bs
  | [], bs => by simp [mulL]
  | a :: as, bs => by
    have ⟨r1, _⟩ := mulAddRow_spec a bs 0
    have ⟨t1, _, _⟩ := addc_spec (mulAddRow a bs 0) (0 :: mulL as bs) 0 (by simp)
    have ih := mulL_spec as bs
    simp only [mulL, val_append, val_cons, val_nil, ih] at *
    simp at r1 t1
    grind

end Secp
