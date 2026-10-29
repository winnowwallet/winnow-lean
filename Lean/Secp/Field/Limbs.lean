/-! # 64-bit limb primitives

The three operations every multi-limb routine is built from, each with its exact meaning over
`Nat`: a 64 × 64 → 128-bit multiply, an add with carry and a subtract with borrow. Carries and
borrows are `UInt64` values that the theorems pin to 0 or 1. -/

namespace Secp

def mask32 : UInt64 := 0xFFFFFFFF

/-- The full 128-bit product as (high, low), from four 32 × 32 → 64-bit products. -/
def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& mask32; let a1 := a >>> 32
  let b0 := b &&& mask32; let b1 := b >>> 32
  let p00 := a0 * b0; let p01 := a0 * b1; let p10 := a1 * b0; let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& mask32) + (p10 &&& mask32)
  let lo := (p00 &&& mask32) + (mid <<< 32)
  let hi := p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)
  (hi, lo)

/-- `a + b + c` as (sum mod 2^64, carry). -/
def adc (a b c : UInt64) : UInt64 × UInt64 :=
  let s1 := a + b
  let k1 : UInt64 := if s1 < a then 1 else 0
  let s2 := s1 + c
  let k2 : UInt64 := if s2 < s1 then 1 else 0
  (s2, k1 + k2)

/-- `a - b - c` as (difference mod 2^64, borrow). -/
def sbb (a b c : UInt64) : UInt64 × UInt64 :=
  let d1 := a - b
  let k1 : UInt64 := if a < b then 1 else 0
  let d2 := d1 - c
  let k2 : UInt64 := if d1 < c then 1 else 0
  (d2, k1 + k2)

theorem toNat_and_mask (x : UInt64) : (x &&& mask32).toNat = x.toNat % 2^32 := by
  simp [mask32, UInt64.toNat_and]
  rw [show (4294967295 : Nat) = 2^32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem mulWide_spec (a b : UInt64) :
    (mulWide a b).1.toNat * 2^64 + (mulWide a b).2.toNat = a.toNat * b.toNat := by
  simp only [mulWide, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, toNat_and_mask, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have ha := a.toNat_lt; have hb := b.toNat_lt
  generalize a.toNat = A at *; generalize b.toNat = B at *
  simp only [show (32 : UInt64).toNat % 64 = 32 by rfl]
  have hA : A = (A / 2^32) * 2^32 + A % 2^32 := by omega
  have hB : B = (B / 2^32) * 2^32 + B % 2^32 := by omega
  have h0 : A % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have h1 : A / 2^32 < 2^32 := by omega
  have h2 : B % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have h3 : B / 2^32 < 2^32 := by omega
  have m (x y : Nat) (hx : x < 2^32) (hy : y < 2^32) : x * y % 2^64 = x * y :=
    Nat.mod_eq_of_lt (by have := Nat.mul_lt_mul'' hx hy; simpa using this)
  have mb (x y : Nat) (hx : x < 2^32) (hy : y < 2^32) : x * y ≤ (2^32 - 1) * (2^32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [m _ _ h0 h2, m _ _ h0 h3, m _ _ h1 h2, m _ _ h1 h3]
  have := mb _ _ h0 h2; have := mb _ _ h0 h3; have := mb _ _ h1 h2; have := mb _ _ h1 h3
  generalize A / 2^32 = a1 at *; generalize A % 2^32 = a0 at *
  generalize B / 2^32 = b1 at *; generalize B % 2^32 = b0 at *
  subst hA hB
  grind

/-- The high word of a product is at most 2^64 − 2, so adding a carry to it cannot overflow. -/
theorem mulWide_hi_le (a b : UInt64) : (mulWide a b).1.toNat ≤ 2^64 - 2 := by
  have h := mulWide_spec a b
  have hl := (mulWide a b).2.toNat_lt
  have hp : a.toNat * b.toNat ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by have := a.toNat_lt; omega) (by have := b.toNat_lt; omega)
  omega

theorem adc_spec (a b c : UInt64) (hc : c.toNat ≤ 1) :
    (adc a b c).1.toNat + (adc a b c).2.toNat * 2^64 = a.toNat + b.toNat + c.toNat
      ∧ (adc a b c).2.toNat ≤ 1 := by
  simp only [adc]
  have ha := a.toNat_lt; have hb := b.toNat_lt
  split <;> split <;>
    simp_all [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] <;> omega

theorem sbb_spec (a b c : UInt64) (hc : c.toNat ≤ 1) :
    (sbb a b c).1.toNat + b.toNat + c.toNat = a.toNat + (sbb a b c).2.toNat * 2^64
      ∧ (sbb a b c).2.toNat ≤ 1 := by
  simp only [sbb]
  have ha := a.toNat_lt; have hb := b.toNat_lt
  split <;> split <;>
    simp_all [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub] <;> omega

end Secp
