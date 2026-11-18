import SecpCt.ScalarProofs

/-! # Scalar multiplication

`Sc.mul` multiplies two four-word numbers into eight words and brings them below N in three folds and one
last subtraction. Its loops run over arrays, but every size in them is fixed by the code, so for the sizes
that occur each loop is a fixed list of word operations. The proofs below unroll each loop for its size and
then argue about numbers, as the field's proofs do.

Most of this file is written by a script and is not meant to be read line by line: the long middle of each
proof names the result of every word operation in the order the loop does them, and the lemmas with many
variables say that those operations add up. What each theorem about `Sc` says is short, and is meant to be
read. -/

namespace SecpCt

/-- The number a list of words stands for, least significant first. -/
def digits : List UInt64 → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * digits ws

/-- Four words and then the rest: the rest counts 2²⁵⁶ times. -/
theorem digits_split (u0 u1 u2 u3 : UInt64) (rest : List UInt64) :
    digits (u0 :: u1 :: u2 :: u3 :: rest) = value u0 u1 u2 u3 + 2 ^ 256 * digits rest := by
  simp only [digits, value, Nat.reducePow]
  omega

/-- The eight words `mulWords` makes of two four-word numbers are their product. -/
theorem mulWords_spec (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    ∃ t0 t1 t2 t3 t4 t5 t6 t7, Sc.mulWords #[a0, a1, a2, a3] #[b0, b1, b2, b3] = #[t0, t1, t2, t3, t4, t5, t6, t7]
      ∧ digits [t0, t1, t2, t3, t4, t5, t6, t7] = value a0 a1 a2 a3 * value b0 b1 b2 b3 := by
  simp only [Sc.mulWords]
  simp [List.range'_succ, show Array.replicate 8 (0 : UInt64) = #[0, 0, 0, 0, 0, 0, 0, 0] from rfl]
  refine ⟨_, _, _, _, _, _, _, _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have e3 := mulAdd_spec a0 b0 0 0
  generalize (mulAdd a0 b0 0 0).1 = h1 at *
  generalize (mulAdd a0 b0 0 0).2 = l2 at *
  have e6 := mulAdd_spec a0 b1 0 h1
  generalize (mulAdd a0 b1 0 h1).1 = h4 at *
  generalize (mulAdd a0 b1 0 h1).2 = l5 at *
  have e9 := mulAdd_spec a0 b2 0 h4
  generalize (mulAdd a0 b2 0 h4).1 = h7 at *
  generalize (mulAdd a0 b2 0 h4).2 = l8 at *
  have e12 := mulAdd_spec a0 b3 0 h7
  generalize (mulAdd a0 b3 0 h7).1 = h10 at *
  generalize (mulAdd a0 b3 0 h7).2 = l11 at *
  have e15 := mulAdd_spec a1 b0 l5 0
  generalize (mulAdd a1 b0 l5 0).1 = h13 at *
  generalize (mulAdd a1 b0 l5 0).2 = l14 at *
  have e18 := mulAdd_spec a1 b1 l8 h13
  generalize (mulAdd a1 b1 l8 h13).1 = h16 at *
  generalize (mulAdd a1 b1 l8 h13).2 = l17 at *
  have e21 := mulAdd_spec a1 b2 l11 h16
  generalize (mulAdd a1 b2 l11 h16).1 = h19 at *
  generalize (mulAdd a1 b2 l11 h16).2 = l20 at *
  have e24 := mulAdd_spec a1 b3 h10 h19
  generalize (mulAdd a1 b3 h10 h19).1 = h22 at *
  generalize (mulAdd a1 b3 h10 h19).2 = l23 at *
  have e27 := mulAdd_spec a2 b0 l17 0
  generalize (mulAdd a2 b0 l17 0).1 = h25 at *
  generalize (mulAdd a2 b0 l17 0).2 = l26 at *
  have e30 := mulAdd_spec a2 b1 l20 h25
  generalize (mulAdd a2 b1 l20 h25).1 = h28 at *
  generalize (mulAdd a2 b1 l20 h25).2 = l29 at *
  have e33 := mulAdd_spec a2 b2 l23 h28
  generalize (mulAdd a2 b2 l23 h28).1 = h31 at *
  generalize (mulAdd a2 b2 l23 h28).2 = l32 at *
  have e36 := mulAdd_spec a2 b3 h22 h31
  generalize (mulAdd a2 b3 h22 h31).1 = h34 at *
  generalize (mulAdd a2 b3 h22 h31).2 = l35 at *
  have e39 := mulAdd_spec a3 b0 l29 0
  generalize (mulAdd a3 b0 l29 0).1 = h37 at *
  generalize (mulAdd a3 b0 l29 0).2 = l38 at *
  have e42 := mulAdd_spec a3 b1 l32 h37
  generalize (mulAdd a3 b1 l32 h37).1 = h40 at *
  generalize (mulAdd a3 b1 l32 h37).2 = l41 at *
  have e45 := mulAdd_spec a3 b2 l35 h40
  generalize (mulAdd a3 b2 l35 h40).1 = h43 at *
  generalize (mulAdd a3 b2 l35 h40).2 = l44 at *
  have e48 := mulAdd_spec a3 b3 h34 h43
  generalize (mulAdd a3 b3 h34 h43).1 = h46 at *
  generalize (mulAdd a3 b3 h34 h43).2 = l47 at *
  have expand := product_by_words a0.toNat a1.toNat a2.toNat a3.toNat b0.toNat b1.toNat b2.toNat b3.toNat (2 ^ 64)
  simp only [digits, value, show (0 : UInt64).toNat = 0 from rfl, Nat.reducePow, Nat.add_zero, Nat.mul_zero] at *
  rw [expand]
  omega

set_option exponentiation.threshold 512 in
/-- The words of the high part times `2²⁵⁶ − N` are that product. -/
theorem fold_eight_product (h1 l2 t4 c0 z0 h4 l5 c1 h7 l8 c2 h10 l11 t5 h13 l14 h16 l17 h19 l20 t6 h22 l23 h25 l26 h28 l29 t7 h31 l32 h34 l35 : Nat)
    (is_z0 : z0 = 0)
    (is_c0 : c0 = 4624529908474429119)
    (is_c1 : c1 = 4994812053365940164)
    (is_c2 : c2 = 1)
    (e3 : h1 * 2 ^ 64 + l2 = t4 * c0 + z0 + z0)
    (e6 : h4 * 2 ^ 64 + l5 = t4 * c1 + z0 + h1)
    (e9 : h7 * 2 ^ 64 + l8 = t4 * c2 + z0 + h4)
    (e12 : h10 * 2 ^ 64 + l11 = t5 * c0 + l5 + z0)
    (e15 : h13 * 2 ^ 64 + l14 = t5 * c1 + l8 + h10)
    (e18 : h16 * 2 ^ 64 + l17 = t5 * c2 + h7 + h13)
    (e21 : h19 * 2 ^ 64 + l20 = t6 * c0 + l14 + z0)
    (e24 : h22 * 2 ^ 64 + l23 = t6 * c1 + l17 + h19)
    (e27 : h25 * 2 ^ 64 + l26 = t6 * c2 + h16 + h22)
    (e30 : h28 * 2 ^ 64 + l29 = t7 * c0 + l23 + z0)
    (e33 : h31 * 2 ^ 64 + l32 = t7 * c1 + l26 + h28)
    (e36 : h34 * 2 ^ 64 + l35 = t7 * c2 + h25 + h31) :
    l2 + 2 ^ 64 * (l11 + 2 ^ 64 * (l20 + 2 ^ 64 * (l29 + 2 ^ 64 * (l32 + 2 ^ 64 * (l35 + 2 ^ 64 * (h34 + 2 ^ 64 * (0))))))) = (t4 + 2 ^ 64 * (t5 + 2 ^ 64 * (t6 + 2 ^ 64 * (t7 + 2 ^ 64 * (0))))) * (2 ^ 256 - N) := by
  subst is_z0 is_c0 is_c1 is_c2
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

set_option exponentiation.threshold 512 in
/-- The words of the sum, and its carry out, are the sum. -/
theorem fold_eight_sum (s37 k38 t0 l2 z0 s41 k42 t1 l11 s45 k46 t2 l20 s49 k50 t3 l29 s53 k54 l32 s57 k58 l35 s61 k62 h34 : Nat)
    (is_z0 : z0 = 0)
    (e39 : s37 + k38 * 2 ^ 64 = t0 + l2 + z0)
    (e43 : s41 + k42 * 2 ^ 64 = t1 + l11 + k38)
    (e47 : s45 + k46 * 2 ^ 64 = t2 + l20 + k42)
    (e51 : s49 + k50 * 2 ^ 64 = t3 + l29 + k46)
    (e55 : s53 + k54 * 2 ^ 64 = z0 + l32 + k50)
    (e59 : s57 + k58 * 2 ^ 64 = z0 + l35 + k54)
    (e63 : s61 + k62 * 2 ^ 64 = z0 + h34 + k58) :
    s37 + 2 ^ 64 * (s41 + 2 ^ 64 * (s45 + 2 ^ 64 * (s49 + 2 ^ 64 * (s53 + 2 ^ 64 * (s57 + 2 ^ 64 * (s61 + 2 ^ 64 * (0))))))) + k62 * 2 ^ 448 = t0 + 2 ^ 64 * (t1 + 2 ^ 64 * (t2 + 2 ^ 64 * (t3 + 2 ^ 64 * (0)))) + (l2 + 2 ^ 64 * (l11 + 2 ^ 64 * (l20 + 2 ^ 64 * (l29 + 2 ^ 64 * (l32 + 2 ^ 64 * (l35 + 2 ^ 64 * (h34 + 2 ^ 64 * (0)))))))) := by
  subst is_z0
  simp only [Nat.reducePow] at *
  omega

set_option exponentiation.threshold 512 in
/-- With the words read as numbers: the sum has no carry out and nothing of the product was left out. -/
theorem fold_eight_fits (P Pl S L H k : Nat)
    (product : P = H * (2 ^ 256 - N))
    (sum : S + k * 2 ^ 448 = L + Pl)
    (lowBound : L < 2 ^ 256)
    (highBound : H < 2 ^ 256)
    (carry : k ≤ 1)
    (whole : P = Pl) :
    S = L + H * (2 ^ 256 - N) := by
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

set_option exponentiation.threshold 512 in
/-- The first fold: eight words to seven, the high four folded in as `2²⁵⁶ − N` times themselves. Nothing is dropped, because the sum is below 2³⁸⁶. -/
theorem fold_eight (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) :
    ∃ f0 f1 f2 f3 f4 f5 f6, Sc.fold #[t0, t1, t2, t3, t4, t5, t6, t7] 7 = #[f0, f1, f2, f3, f4, f5, f6]
      ∧ digits [f0, f1, f2, f3, f4, f5, f6] = digits [t0, t1, t2, t3] + digits [t4, t5, t6, t7] * (2 ^ 256 - N) := by
  simp only [Sc.fold, Sc.mulWords, Sc.addWords, Sc.complement]
  simp [List.range'_succ, show Array.replicate 7 (0 : UInt64) = #[0, 0, 0, 0, 0, 0, 0] from rfl]
  refine ⟨_, _, _, _, _, _, _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have e3 := mulAdd_spec t4 4624529908474429119 0 0
  generalize (mulAdd t4 4624529908474429119 0 0).1 = h1 at *
  generalize (mulAdd t4 4624529908474429119 0 0).2 = l2 at *
  have e6 := mulAdd_spec t4 4994812053365940164 0 h1
  generalize (mulAdd t4 4994812053365940164 0 h1).1 = h4 at *
  generalize (mulAdd t4 4994812053365940164 0 h1).2 = l5 at *
  have e9 := mulAdd_spec t4 1 0 h4
  generalize (mulAdd t4 1 0 h4).1 = h7 at *
  generalize (mulAdd t4 1 0 h4).2 = l8 at *
  have e12 := mulAdd_spec t5 4624529908474429119 l5 0
  generalize (mulAdd t5 4624529908474429119 l5 0).1 = h10 at *
  generalize (mulAdd t5 4624529908474429119 l5 0).2 = l11 at *
  have e15 := mulAdd_spec t5 4994812053365940164 l8 h10
  generalize (mulAdd t5 4994812053365940164 l8 h10).1 = h13 at *
  generalize (mulAdd t5 4994812053365940164 l8 h10).2 = l14 at *
  have e18 := mulAdd_spec t5 1 h7 h13
  generalize (mulAdd t5 1 h7 h13).1 = h16 at *
  generalize (mulAdd t5 1 h7 h13).2 = l17 at *
  have e21 := mulAdd_spec t6 4624529908474429119 l14 0
  generalize (mulAdd t6 4624529908474429119 l14 0).1 = h19 at *
  generalize (mulAdd t6 4624529908474429119 l14 0).2 = l20 at *
  have e24 := mulAdd_spec t6 4994812053365940164 l17 h19
  generalize (mulAdd t6 4994812053365940164 l17 h19).1 = h22 at *
  generalize (mulAdd t6 4994812053365940164 l17 h19).2 = l23 at *
  have e27 := mulAdd_spec t6 1 h16 h22
  generalize (mulAdd t6 1 h16 h22).1 = h25 at *
  generalize (mulAdd t6 1 h16 h22).2 = l26 at *
  have e30 := mulAdd_spec t7 4624529908474429119 l23 0
  generalize (mulAdd t7 4624529908474429119 l23 0).1 = h28 at *
  generalize (mulAdd t7 4624529908474429119 l23 0).2 = l29 at *
  have e33 := mulAdd_spec t7 4994812053365940164 l26 h28
  generalize (mulAdd t7 4994812053365940164 l26 h28).1 = h31 at *
  generalize (mulAdd t7 4994812053365940164 l26 h28).2 = l32 at *
  have e36 := mulAdd_spec t7 1 h25 h31
  generalize (mulAdd t7 1 h25 h31).1 = h34 at *
  generalize (mulAdd t7 1 h25 h31).2 = l35 at *
  obtain ⟨e39, hk40⟩ := adc_spec t0 l2 0 (by decide)
  generalize (adc t0 l2 0).1 = s37 at *
  generalize (adc t0 l2 0).2 = k38 at *
  obtain ⟨e43, hk44⟩ := adc_spec t1 l11 k38 (by simpa [UInt64.le_iff_toNat_le] using hk40)
  generalize (adc t1 l11 k38).1 = s41 at *
  generalize (adc t1 l11 k38).2 = k42 at *
  obtain ⟨e47, hk48⟩ := adc_spec t2 l20 k42 (by simpa [UInt64.le_iff_toNat_le] using hk44)
  generalize (adc t2 l20 k42).1 = s45 at *
  generalize (adc t2 l20 k42).2 = k46 at *
  obtain ⟨e51, hk52⟩ := adc_spec t3 l29 k46 (by simpa [UInt64.le_iff_toNat_le] using hk48)
  generalize (adc t3 l29 k46).1 = s49 at *
  generalize (adc t3 l29 k46).2 = k50 at *
  obtain ⟨e55, hk56⟩ := adc_spec 0 l32 k50 (by simpa [UInt64.le_iff_toNat_le] using hk52)
  generalize (adc 0 l32 k50).1 = s53 at *
  generalize (adc 0 l32 k50).2 = k54 at *
  obtain ⟨e59, hk60⟩ := adc_spec 0 l35 k54 (by simpa [UInt64.le_iff_toNat_le] using hk56)
  generalize (adc 0 l35 k54).1 = s57 at *
  generalize (adc 0 l35 k54).2 = k58 at *
  obtain ⟨e63, hk64⟩ := adc_spec 0 h34 k58 (by simpa [UInt64.le_iff_toNat_le] using hk60)
  generalize (adc 0 h34 k58).1 = s61 at *
  generalize (adc 0 h34 k58).2 = k62 at *
  have product : digits [l2, l11, l20, l29, l32, l35, h34] = digits [t4, t5, t6, t7] * (2 ^ 256 - N) := by
    simp only [digits]
    exact fold_eight_product _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl e3 e6 e9 e12 e15 e18 e21 e24 e27 e30 e33 e36
  have sum : digits [s37, s41, s45, s49, s53, s57, s61] + k62.toNat * 2 ^ 448 = digits [t0, t1, t2, t3] + digits [l2, l11, l20, l29, l32, l35, h34] := by
    simp only [digits]
    exact fold_eight_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl e39 e43 e47 e51 e55 e59 e63
  have whole : digits [l2, l11, l20, l29, l32, l35, h34] = digits [l2, l11, l20, l29, l32, l35, h34] := rfl
  have lowBound : digits [t0, t1, t2, t3] < 2 ^ 256 := by
    have := t0.toNat_lt
    have := t1.toNat_lt
    have := t2.toNat_lt
    have := t3.toNat_lt
    simp only [digits, Nat.reducePow]
    omega
  have highBound : digits [t4, t5, t6, t7] < 2 ^ 256 := by
    have := t4.toNat_lt
    have := t5.toNat_lt
    have := t6.toNat_lt
    have := t7.toNat_lt
    simp only [digits, Nat.reducePow] at *
    omega
  exact fold_eight_fits _ _ _ _ _ _ product sum lowBound highBound hk64 whole

set_option exponentiation.threshold 512 in
/-- The words of the high part times `2²⁵⁶ − N` are that product. -/
theorem fold_seven_product (h1 l2 t4 c0 z0 h4 l5 c1 h7 l8 c2 h10 l11 t5 h13 l14 h16 l17 h19 l20 t6 h22 l23 h25 l26 : Nat)
    (is_z0 : z0 = 0)
    (is_c0 : c0 = 4624529908474429119)
    (is_c1 : c1 = 4994812053365940164)
    (is_c2 : c2 = 1)
    (e3 : h1 * 2 ^ 64 + l2 = t4 * c0 + z0 + z0)
    (e6 : h4 * 2 ^ 64 + l5 = t4 * c1 + z0 + h1)
    (e9 : h7 * 2 ^ 64 + l8 = t4 * c2 + z0 + h4)
    (e12 : h10 * 2 ^ 64 + l11 = t5 * c0 + l5 + z0)
    (e15 : h13 * 2 ^ 64 + l14 = t5 * c1 + l8 + h10)
    (e18 : h16 * 2 ^ 64 + l17 = t5 * c2 + h7 + h13)
    (e21 : h19 * 2 ^ 64 + l20 = t6 * c0 + l14 + z0)
    (e24 : h22 * 2 ^ 64 + l23 = t6 * c1 + l17 + h19)
    (e27 : h25 * 2 ^ 64 + l26 = t6 * c2 + h16 + h22) :
    l2 + 2 ^ 64 * (l11 + 2 ^ 64 * (l20 + 2 ^ 64 * (l23 + 2 ^ 64 * (l26 + 2 ^ 64 * (h25 + 2 ^ 64 * (0)))))) = (t4 + 2 ^ 64 * (t5 + 2 ^ 64 * (t6 + 2 ^ 64 * (0)))) * (2 ^ 256 - N) := by
  subst is_z0 is_c0 is_c1 is_c2
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

set_option exponentiation.threshold 512 in
/-- The words of the sum, and its carry out, are the sum. -/
theorem fold_seven_sum (s28 k29 t0 l2 z0 s32 k33 t1 l11 s36 k37 t2 l20 s40 k41 t3 l23 s44 k45 l26 : Nat)
    (is_z0 : z0 = 0)
    (e30 : s28 + k29 * 2 ^ 64 = t0 + l2 + z0)
    (e34 : s32 + k33 * 2 ^ 64 = t1 + l11 + k29)
    (e38 : s36 + k37 * 2 ^ 64 = t2 + l20 + k33)
    (e42 : s40 + k41 * 2 ^ 64 = t3 + l23 + k37)
    (e46 : s44 + k45 * 2 ^ 64 = z0 + l26 + k41) :
    s28 + 2 ^ 64 * (s32 + 2 ^ 64 * (s36 + 2 ^ 64 * (s40 + 2 ^ 64 * (s44 + 2 ^ 64 * (0))))) + k45 * 2 ^ 320 = t0 + 2 ^ 64 * (t1 + 2 ^ 64 * (t2 + 2 ^ 64 * (t3 + 2 ^ 64 * (0)))) + (l2 + 2 ^ 64 * (l11 + 2 ^ 64 * (l20 + 2 ^ 64 * (l23 + 2 ^ 64 * (l26 + 2 ^ 64 * (0)))))) := by
  subst is_z0
  simp only [Nat.reducePow] at *
  omega

set_option exponentiation.threshold 512 in
/-- With the words read as numbers: the sum has no carry out and nothing of the product was left out. -/
theorem fold_seven_fits (P Pl D S L H k : Nat)
    (product : P = H * (2 ^ 256 - N))
    (sum : S + k * 2 ^ 320 = L + Pl)
    (lowBound : L < 2 ^ 256)
    (highBound : H < 2 ^ 130)
    (carry : k ≤ 1)
    (whole : P = Pl + 2 ^ 320 * D) :
    S = L + H * (2 ^ 256 - N) := by
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

set_option exponentiation.threshold 512 in
/-- The second fold: seven words to five. The sum fits when the high three words are below 2¹³⁰, which they are after the first fold. -/
theorem fold_seven (t0 t1 t2 t3 t4 t5 t6 : UInt64) (high : digits [t4, t5, t6] < 2 ^ 130) :
    ∃ f0 f1 f2 f3 f4, Sc.fold #[t0, t1, t2, t3, t4, t5, t6] 5 = #[f0, f1, f2, f3, f4]
      ∧ digits [f0, f1, f2, f3, f4] = digits [t0, t1, t2, t3] + digits [t4, t5, t6] * (2 ^ 256 - N) := by
  simp only [Sc.fold, Sc.mulWords, Sc.addWords, Sc.complement]
  simp [List.range'_succ, show Array.replicate 5 (0 : UInt64) = #[0, 0, 0, 0, 0] from rfl, show Array.replicate 6 (0 : UInt64) = #[0, 0, 0, 0, 0, 0] from rfl]
  refine ⟨_, _, _, _, _, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have e3 := mulAdd_spec t4 4624529908474429119 0 0
  generalize (mulAdd t4 4624529908474429119 0 0).1 = h1 at *
  generalize (mulAdd t4 4624529908474429119 0 0).2 = l2 at *
  have e6 := mulAdd_spec t4 4994812053365940164 0 h1
  generalize (mulAdd t4 4994812053365940164 0 h1).1 = h4 at *
  generalize (mulAdd t4 4994812053365940164 0 h1).2 = l5 at *
  have e9 := mulAdd_spec t4 1 0 h4
  generalize (mulAdd t4 1 0 h4).1 = h7 at *
  generalize (mulAdd t4 1 0 h4).2 = l8 at *
  have e12 := mulAdd_spec t5 4624529908474429119 l5 0
  generalize (mulAdd t5 4624529908474429119 l5 0).1 = h10 at *
  generalize (mulAdd t5 4624529908474429119 l5 0).2 = l11 at *
  have e15 := mulAdd_spec t5 4994812053365940164 l8 h10
  generalize (mulAdd t5 4994812053365940164 l8 h10).1 = h13 at *
  generalize (mulAdd t5 4994812053365940164 l8 h10).2 = l14 at *
  have e18 := mulAdd_spec t5 1 h7 h13
  generalize (mulAdd t5 1 h7 h13).1 = h16 at *
  generalize (mulAdd t5 1 h7 h13).2 = l17 at *
  have e21 := mulAdd_spec t6 4624529908474429119 l14 0
  generalize (mulAdd t6 4624529908474429119 l14 0).1 = h19 at *
  generalize (mulAdd t6 4624529908474429119 l14 0).2 = l20 at *
  have e24 := mulAdd_spec t6 4994812053365940164 l17 h19
  generalize (mulAdd t6 4994812053365940164 l17 h19).1 = h22 at *
  generalize (mulAdd t6 4994812053365940164 l17 h19).2 = l23 at *
  have e27 := mulAdd_spec t6 1 h16 h22
  generalize (mulAdd t6 1 h16 h22).1 = h25 at *
  generalize (mulAdd t6 1 h16 h22).2 = l26 at *
  obtain ⟨e30, hk31⟩ := adc_spec t0 l2 0 (by decide)
  generalize (adc t0 l2 0).1 = s28 at *
  generalize (adc t0 l2 0).2 = k29 at *
  obtain ⟨e34, hk35⟩ := adc_spec t1 l11 k29 (by simpa [UInt64.le_iff_toNat_le] using hk31)
  generalize (adc t1 l11 k29).1 = s32 at *
  generalize (adc t1 l11 k29).2 = k33 at *
  obtain ⟨e38, hk39⟩ := adc_spec t2 l20 k33 (by simpa [UInt64.le_iff_toNat_le] using hk35)
  generalize (adc t2 l20 k33).1 = s36 at *
  generalize (adc t2 l20 k33).2 = k37 at *
  obtain ⟨e42, hk43⟩ := adc_spec t3 l23 k37 (by simpa [UInt64.le_iff_toNat_le] using hk39)
  generalize (adc t3 l23 k37).1 = s40 at *
  generalize (adc t3 l23 k37).2 = k41 at *
  obtain ⟨e46, hk47⟩ := adc_spec 0 l26 k41 (by simpa [UInt64.le_iff_toNat_le] using hk43)
  generalize (adc 0 l26 k41).1 = s44 at *
  generalize (adc 0 l26 k41).2 = k45 at *
  have product : digits [l2, l11, l20, l23, l26, h25] = digits [t4, t5, t6] * (2 ^ 256 - N) := by
    simp only [digits]
    exact fold_seven_product _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl e3 e6 e9 e12 e15 e18 e21 e24 e27
  have sum : digits [s28, s32, s36, s40, s44] + k45.toNat * 2 ^ 320 = digits [t0, t1, t2, t3] + digits [l2, l11, l20, l23, l26] := by
    simp only [digits]
    exact fold_seven_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl e30 e34 e38 e42 e46
  have whole : digits [l2, l11, l20, l23, l26, h25] = digits [l2, l11, l20, l23, l26] + 2 ^ 320 * digits [h25] := by
    simp only [digits, Nat.reducePow]
    omega
  have lowBound : digits [t0, t1, t2, t3] < 2 ^ 256 := by
    have := t0.toNat_lt
    have := t1.toNat_lt
    have := t2.toNat_lt
    have := t3.toNat_lt
    simp only [digits, Nat.reducePow]
    omega
  have highBound : digits [t4, t5, t6] < 2 ^ 130 := by
    have := t4.toNat_lt
    have := t5.toNat_lt
    have := t6.toNat_lt
    simp only [digits, Nat.reducePow] at *
    omega
  exact fold_seven_fits _ _ (digits [h25]) _ _ _ _ product sum lowBound highBound hk47 whole

set_option exponentiation.threshold 512 in
/-- The words of the high part times `2²⁵⁶ − N` are that product. -/
theorem fold_five_product (h1 l2 t4 c0 z0 h4 l5 c1 h7 l8 c2 : Nat)
    (is_z0 : z0 = 0)
    (is_c0 : c0 = 4624529908474429119)
    (is_c1 : c1 = 4994812053365940164)
    (is_c2 : c2 = 1)
    (e3 : h1 * 2 ^ 64 + l2 = t4 * c0 + z0 + z0)
    (e6 : h4 * 2 ^ 64 + l5 = t4 * c1 + z0 + h1)
    (e9 : h7 * 2 ^ 64 + l8 = t4 * c2 + z0 + h4) :
    l2 + 2 ^ 64 * (l5 + 2 ^ 64 * (l8 + 2 ^ 64 * (h7 + 2 ^ 64 * (0)))) = (t4 + 2 ^ 64 * (0)) * (2 ^ 256 - N) := by
  subst is_z0 is_c0 is_c1 is_c2
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

set_option exponentiation.threshold 512 in
/-- The words of the sum, and its carry out, are the sum. -/
theorem fold_five_sum (s10 k11 t0 l2 z0 s14 k15 t1 l5 s18 k19 t2 l8 s22 k23 t3 h7 s26 k27 : Nat)
    (is_z0 : z0 = 0)
    (e12 : s10 + k11 * 2 ^ 64 = t0 + l2 + z0)
    (e16 : s14 + k15 * 2 ^ 64 = t1 + l5 + k11)
    (e20 : s18 + k19 * 2 ^ 64 = t2 + l8 + k15)
    (e24 : s22 + k23 * 2 ^ 64 = t3 + h7 + k19)
    (e28 : s26 + k27 * 2 ^ 64 = z0 + z0 + k23) :
    s10 + 2 ^ 64 * (s14 + 2 ^ 64 * (s18 + 2 ^ 64 * (s22 + 2 ^ 64 * (s26 + 2 ^ 64 * (0))))) + k27 * 2 ^ 320 = t0 + 2 ^ 64 * (t1 + 2 ^ 64 * (t2 + 2 ^ 64 * (t3 + 2 ^ 64 * (0)))) + (l2 + 2 ^ 64 * (l5 + 2 ^ 64 * (l8 + 2 ^ 64 * (h7 + 2 ^ 64 * (0))))) := by
  subst is_z0
  simp only [Nat.reducePow] at *
  omega

set_option exponentiation.threshold 512 in
/-- With the words read as numbers: the sum has no carry out and nothing of the product was left out. -/
theorem fold_five_fits (P Pl S L H k : Nat)
    (product : P = H * (2 ^ 256 - N))
    (sum : S + k * 2 ^ 320 = L + Pl)
    (lowBound : L < 2 ^ 256)
    (highBound : H < 2 ^ 64)
    (carry : k ≤ 1)
    (whole : P = Pl) :
    S = L + H * (2 ^ 256 - N) := by
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

set_option exponentiation.threshold 512 in
/-- The third fold: five words to five, the fifth folded in. It always fits. -/
theorem fold_five (t0 t1 t2 t3 t4 : UInt64) :
    ∃ f0 f1 f2 f3 f4, Sc.fold #[t0, t1, t2, t3, t4] 5 = #[f0, f1, f2, f3, f4]
      ∧ digits [f0, f1, f2, f3, f4] = digits [t0, t1, t2, t3] + digits [t4] * (2 ^ 256 - N) := by
  simp only [Sc.fold, Sc.mulWords, Sc.addWords, Sc.complement]
  simp [List.range'_succ, show Array.replicate 4 (0 : UInt64) = #[0, 0, 0, 0] from rfl, show Array.replicate 5 (0 : UInt64) = #[0, 0, 0, 0, 0] from rfl]
  refine ⟨_, _, _, _, _, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have e3 := mulAdd_spec t4 4624529908474429119 0 0
  generalize (mulAdd t4 4624529908474429119 0 0).1 = h1 at *
  generalize (mulAdd t4 4624529908474429119 0 0).2 = l2 at *
  have e6 := mulAdd_spec t4 4994812053365940164 0 h1
  generalize (mulAdd t4 4994812053365940164 0 h1).1 = h4 at *
  generalize (mulAdd t4 4994812053365940164 0 h1).2 = l5 at *
  have e9 := mulAdd_spec t4 1 0 h4
  generalize (mulAdd t4 1 0 h4).1 = h7 at *
  generalize (mulAdd t4 1 0 h4).2 = l8 at *
  obtain ⟨e12, hk13⟩ := adc_spec t0 l2 0 (by decide)
  generalize (adc t0 l2 0).1 = s10 at *
  generalize (adc t0 l2 0).2 = k11 at *
  obtain ⟨e16, hk17⟩ := adc_spec t1 l5 k11 (by simpa [UInt64.le_iff_toNat_le] using hk13)
  generalize (adc t1 l5 k11).1 = s14 at *
  generalize (adc t1 l5 k11).2 = k15 at *
  obtain ⟨e20, hk21⟩ := adc_spec t2 l8 k15 (by simpa [UInt64.le_iff_toNat_le] using hk17)
  generalize (adc t2 l8 k15).1 = s18 at *
  generalize (adc t2 l8 k15).2 = k19 at *
  obtain ⟨e24, hk25⟩ := adc_spec t3 h7 k19 (by simpa [UInt64.le_iff_toNat_le] using hk21)
  generalize (adc t3 h7 k19).1 = s22 at *
  generalize (adc t3 h7 k19).2 = k23 at *
  obtain ⟨e28, hk29⟩ := adc_spec 0 0 k23 (by simpa [UInt64.le_iff_toNat_le] using hk25)
  generalize (adc 0 0 k23).1 = s26 at *
  generalize (adc 0 0 k23).2 = k27 at *
  have product : digits [l2, l5, l8, h7] = digits [t4] * (2 ^ 256 - N) := by
    simp only [digits]
    exact fold_five_product _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl e3 e6 e9
  have sum : digits [s10, s14, s18, s22, s26] + k27.toNat * 2 ^ 320 = digits [t0, t1, t2, t3] + digits [l2, l5, l8, h7] := by
    simp only [digits]
    exact fold_five_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl e12 e16 e20 e24 e28
  have whole : digits [l2, l5, l8, h7] = digits [l2, l5, l8, h7] := rfl
  have lowBound : digits [t0, t1, t2, t3] < 2 ^ 256 := by
    have := t0.toNat_lt
    have := t1.toNat_lt
    have := t2.toNat_lt
    have := t3.toNat_lt
    simp only [digits, Nat.reducePow]
    omega
  have highBound : digits [t4] < 2 ^ 64 := by
    have := t4.toNat_lt
    simp only [digits, Nat.reducePow] at *
    omega
  exact fold_five_fits _ _ _ _ _ _ product sum lowBound highBound hk29 whole

/-- One word is the number it stands for. -/
theorem digits_one (w : UInt64) : digits [w] = w.toNat := by
  simp only [digits, Nat.mul_zero, Nat.add_zero]

/-- Four words are the number `value` gives them. -/
theorem digits_four (u0 u1 u2 u3 : UInt64) : digits [u0, u1, u2, u3] = value u0 u1 u2 u3 := by
  rw [digits_split, show digits [] = 0 from rfl, Nat.mul_zero, Nat.add_zero]

/-- After the first fold, what is above the low four words is below 2¹³⁰. -/
theorem first_fold_high (F1 L0 H0 L1 H1 : Nat) (vB : F1 = L0 + H0 * (2 ^ 256 - N)) (sF : F1 = L1 + 2 ^ 256 * H1)
    (bL0 : L0 < 2 ^ 256) (bH0 : H0 < 2 ^ 256) : H1 < 2 ^ 130 := by
  simp only [N, Nat.reducePow, Nat.reduceSub] at *
  omega

/-- The three folds as numbers. Each takes a multiple of N away, so what is left is the product less a
multiple of N; and it is below 2N, with a fifth word of 0 or 1, which is what `reduceOnce` asks for. -/
theorem folds_finish (AB T L0 H0 F1 L1 H1 F2 L2 G4 F3 Q Q4 : Nat)
    (vA : T = AB) (sT : T = L0 + 2 ^ 256 * H0)
    (vB : F1 = L0 + H0 * (2 ^ 256 - N)) (sF : F1 = L1 + 2 ^ 256 * H1)
    (vC : F2 = L1 + H1 * (2 ^ 256 - N)) (sG : F2 = L2 + 2 ^ 256 * G4)
    (vD : F3 = L2 + G4 * (2 ^ 256 - N)) (sQ : F3 = Q + 2 ^ 256 * Q4)
    (bL0 : L0 < 2 ^ 256) (bH0 : H0 < 2 ^ 256) (bL1 : L1 < 2 ^ 256) (bL2 : L2 < 2 ^ 256) (bQ : Q < 2 ^ 256) :
    Q4 ≤ 1 ∧ Q + Q4 * 2 ^ 256 < 2 * N ∧ AB = Q + Q4 * 2 ^ 256 + N * (H0 + H1 + G4) := by
  simp only [N, Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *
  omega

/-- `a · b` modulo N, for any two scalars. -/
theorem Sc.mul_spec (a b : Sc) : (Sc.mul a b).toNat = (a.toNat * b.toNat) % N := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, hA, vA⟩ := mulWords_spec a.a0 a.a1 a.a2 a.a3 b.a0 b.a1 b.a2 b.a3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, hB, vB⟩ := fold_eight t0 t1 t2 t3 t4 t5 t6 t7
  have sT := digits_split t0 t1 t2 t3 [t4, t5, t6, t7]
  have sF := digits_split f0 f1 f2 f3 [f4, f5, f6]
  rw [digits_four] at vB
  have bL0 := value_lt t0 t1 t2 t3
  have bH0 : digits [t4, t5, t6, t7] < 2 ^ 256 := by
    rw [digits_four]
    exact value_lt t4 t5 t6 t7
  have high := first_fold_high _ _ _ _ _ vB sF bL0 bH0
  obtain ⟨g0, g1, g2, g3, g4, hC, vC⟩ := fold_seven f0 f1 f2 f3 f4 f5 f6 high
  obtain ⟨q0, q1, q2, q3, q4, hD, vD⟩ := fold_five g0 g1 g2 g3 g4
  have sG := digits_split g0 g1 g2 g3 [g4]
  have sQ := digits_split q0 q1 q2 q3 [q4]
  rw [digits_four] at vC vD
  rw [digits_one] at vD sG sQ
  obtain ⟨carry, small, whole⟩ := folds_finish _ _ _ _ _ _ _ _ _ _ _ _ _ vA sT vB sF vC sG vD sQ bL0 bH0
    (value_lt f0 f1 f2 f3) (value_lt g0 g1 g2 g3) (value_lt q0 q1 q2 q3)
  have reduced := reduceOnce_spec q0 q1 q2 q3 q4 carry small
  simp only [Sc.mul, Sc.reduceWide, hA, hB, hC, hD]
  simp only [Sc.toNat] at reduced ⊢
  rw [whole, Nat.add_mul_mod_self_left]
  exact reduced

/-- A product of scalars is below N whatever was multiplied. -/
theorem Sc.mul_lt (a b : Sc) : (Sc.mul a b).toNat < N := by
  rw [Sc.mul_spec]
  exact Nat.mod_lt _ (by decide)

end SecpCt
