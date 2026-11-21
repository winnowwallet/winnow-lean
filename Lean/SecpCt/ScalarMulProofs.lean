import SecpCt.ScalarProofs

/-! # Scalar multiplication, proved compositionally on registers

`Sc.mul` forms an eight-word product by four calls to `mulRow` and reduces it modulo N in three register
folds (`2²⁵⁶ ≡ c0 + 2⁶⁴·c1 + 2¹²⁸ (mod N)`) and `reduceOnce`. Ring identities are discharged over `Int`
(`grind` with zero case splits), and bounds by `omega`. -/

namespace SecpCt

private def valI (W a0 a1 a2 a3 : Int) : Int := a0 + a1 * W + a2 * W ^ 2 + a3 * W ^ 3

private theorem valI_eq (u0 u1 u2 u3 : UInt64) :
    (value u0 u1 u2 u3 : Int) = valI ((2 ^ 64 : Nat) : Int) u0.toNat u1.toNat u2.toNat u3.toNat := by
  simp only [value, valI, Nat.reducePow, Int.natCast_add, Int.natCast_mul]
  rfl

private theorem valI_shift (W x0 x1 x2 x3 x4 : Int) :
    valI W x0 x1 x2 x3 + W ^ 4 * x4 = x0 + W * valI W x1 x2 x3 x4 := by
  simp only [valI]; grind

private theorem valI_split2 (W f0 f1 f2 f3 f4 f5 f6 : Int) :
    valI W f0 f1 f2 f3 + W ^ 4 * valI W f4 f5 f6 0 =
      f0 + f1 * W + W ^ 2 * (valI W f2 f3 f4 f5 + W ^ 4 * f6) := by
  simp only [valI]; grind

private theorem adc4_alg (W v2 v3 v4 v5 t4 t5 t6 t7 f2 k0 f3 k1 f4 k2 f5 f6 : Int)
    (a0 : f2 + k0 * W = v2 + t4)
    (a1 : f3 + k1 * W = v3 + t5 + k0)
    (a2 : f4 + k2 * W = v4 + t6 + k1)
    (a3 : f5 + f6 * W = v5 + t7 + k2) :
    valI W f2 f3 f4 f5 + W ^ 4 * f6 = valI W v2 v3 v4 v5 + valI W t4 t5 t6 t7 := by
  simp only [valI]; grind

private theorem mulRow_alg (W a u0 u1 u2 u3 r0 r1 r2 r3 k0 s0 k1 s1 k2 s2 hi s3 : Int)
    (e0 : k0 * W + s0 = a * u0 + r0)
    (e1 : k1 * W + s1 = a * u1 + r1 + k0)
    (e2 : k2 * W + s2 = a * u2 + r2 + k1)
    (e3 : hi * W + s3 = a * u3 + r3 + k2) :
    valI W s0 s1 s2 s3 + W ^ 4 * hi = a * valI W u0 u1 u2 u3 + valI W r0 r1 r2 r3 := by
  simp only [valI]; grind

/-- `mulRow` computes `a · u + r` in five words. -/
theorem mulRow_spec (a u0 u1 u2 u3 r0 r1 r2 r3 : UInt64) :
    let (s0, s1, s2, s3, hi) := mulRow a u0 u1 u2 u3 r0 r1 r2 r3
    value s0 s1 s2 s3 + 2 ^ 256 * hi.toNat = a.toNat * value u0 u1 u2 u3 + value r0 r1 r2 r3 := by
  simp only [mulRow]
  have e0 := mulAdd_spec a u0 r0 0
  generalize (mulAdd a u0 r0 0).1 = k0 at *
  generalize (mulAdd a u0 r0 0).2 = s0 at *
  have e1 := mulAdd_spec a u1 r1 k0
  generalize (mulAdd a u1 r1 k0).1 = k1 at *
  generalize (mulAdd a u1 r1 k0).2 = s1 at *
  have e2 := mulAdd_spec a u2 r2 k1
  generalize (mulAdd a u2 r2 k1).1 = k2 at *
  generalize (mulAdd a u2 r2 k1).2 = s2 at *
  have e3 := mulAdd_spec a u3 r3 k2
  generalize (mulAdd a u3 r3 k2).1 = hi at *
  generalize (mulAdd a u3 r3 k2).2 = s3 at *
  simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero] at e0
  apply Int.ofNat.inj
  have ie0 : (k0.toNat : Int) * ((2 ^ 64 : Nat) : Int) + s0.toNat = a.toNat * u0.toNat + r0.toNat := by exact_mod_cast e0
  have ie1 : (k1.toNat : Int) * ((2 ^ 64 : Nat) : Int) + s1.toNat = a.toNat * u1.toNat + r1.toNat + k0.toNat := by exact_mod_cast e1
  have ie2 : (k2.toNat : Int) * ((2 ^ 64 : Nat) : Int) + s2.toNat = a.toNat * u2.toNat + r2.toNat + k1.toNat := by exact_mod_cast e2
  have ie3 : (hi.toNat : Int) * ((2 ^ 64 : Nat) : Int) + s3.toNat = a.toNat * u3.toNat + r3.toNat + k2.toNat := by exact_mod_cast e3
  have hw4 : (((2 ^ 256 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 4 := by decide
  simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul, valI_eq, hw4]
  exact mulRow_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ie0 ie1 ie2 ie3

private theorem mulWide4_alg (W a0 a1 a2 a3 B t0 p1 p2 p3 p4 t1 q2 q3 q4 q5 t2 s3 s4 s5 s6 t3 t4 t5 t6 t7 : Int)
    (r0 : valI W t0 p1 p2 p3 + W ^ 4 * p4 = a0 * B)
    (r1 : valI W t1 q2 q3 q4 + W ^ 4 * q5 = a1 * B + valI W p1 p2 p3 p4)
    (r2 : valI W t2 s3 s4 s5 + W ^ 4 * s6 = a2 * B + valI W q2 q3 q4 q5)
    (r3 : valI W t3 t4 t5 t6 + W ^ 4 * t7 = a3 * B + valI W s3 s4 s5 s6) :
    valI W t0 t1 t2 t3 + W ^ 4 * valI W t4 t5 t6 t7 = valI W a0 a1 a2 a3 * B := by
  rw [valI_shift] at r0 r1 r2 r3
  generalize valI W p1 p2 p3 p4 = P1 at r0 r1
  generalize valI W q2 q3 q4 q5 = Q2 at r1 r2
  generalize valI W s3 s4 s5 s6 = S3 at r2 r3
  generalize valI W t4 t5 t6 t7 = T4 at r3 ⊢
  simp only [valI]; grind

/-- Four `mulRow` passes compute the exact 512-bit product of `a` and `b`. -/
theorem mulWide4_spec (a b : Sc) :
    let (t0, t1, t2, t3, t4, t5, t6, t7) := Sc.mulWide4 a b
    value t0 t1 t2 t3 + 2 ^ 256 * value t4 t5 t6 t7 = a.toNat * b.toNat := by
  simp only [Sc.mulWide4]
  have r0 := mulRow_spec a.a0 b.a0 b.a1 b.a2 b.a3 0 0 0 0
  rcases h0 : mulRow a.a0 b.a0 b.a1 b.a2 b.a3 0 0 0 0 with ⟨t0, p1, p2, p3, p4⟩
  rw [h0] at r0; clear h0; dsimp only at r0 ⊢
  have r1 := mulRow_spec a.a1 b.a0 b.a1 b.a2 b.a3 p1 p2 p3 p4
  rcases h1 : mulRow a.a1 b.a0 b.a1 b.a2 b.a3 p1 p2 p3 p4 with ⟨t1, q2, q3, q4, q5⟩
  rw [h1] at r1; clear h1; dsimp only at r1 ⊢
  have r2 := mulRow_spec a.a2 b.a0 b.a1 b.a2 b.a3 q2 q3 q4 q5
  rcases h2 : mulRow a.a2 b.a0 b.a1 b.a2 b.a3 q2 q3 q4 q5 with ⟨t2, s3, s4, s5, s6⟩
  rw [h2] at r2; clear h2; dsimp only at r2 ⊢
  have r3 := mulRow_spec a.a3 b.a0 b.a1 b.a2 b.a3 s3 s4 s5 s6
  rcases h3 : mulRow a.a3 b.a0 b.a1 b.a2 b.a3 s3 s4 s5 s6 with ⟨t3, t4, t5, t6, t7⟩
  rw [h3] at r3; clear h3; dsimp only at r3 ⊢
  rw [show value 0 0 0 0 = 0 from rfl, Nat.add_zero] at r0
  apply Int.ofNat.inj
  have hw4 : (((2 ^ 256 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 4 := by decide
  have ir0 : valI ((2 ^ 64 : Nat) : Int) t0.toNat p1.toNat p2.toNat p3.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * p4.toNat =
      a.a0.toNat * (value b.a0 b.a1 b.a2 b.a3 : Int) := by
    have : ((value t0 p1 p2 p3 + 2 ^ 256 * p4.toNat : Nat) : Int) = ((a.a0.toNat * value b.a0 b.a1 b.a2 b.a3 : Nat) : Int) := by rw [r0]
    simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, hw4] using this
  have ir1 : valI ((2 ^ 64 : Nat) : Int) t1.toNat q2.toNat q3.toNat q4.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * q5.toNat =
      a.a1.toNat * (value b.a0 b.a1 b.a2 b.a3 : Int) + valI ((2 ^ 64 : Nat) : Int) p1.toNat p2.toNat p3.toNat p4.toNat := by
    have : ((value t1 q2 q3 q4 + 2 ^ 256 * q5.toNat : Nat) : Int) = ((a.a1.toNat * value b.a0 b.a1 b.a2 b.a3 + value p1 p2 p3 p4 : Nat) : Int) := by rw [r1]
    simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, hw4] using this
  have ir2 : valI ((2 ^ 64 : Nat) : Int) t2.toNat s3.toNat s4.toNat s5.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * s6.toNat =
      a.a2.toNat * (value b.a0 b.a1 b.a2 b.a3 : Int) + valI ((2 ^ 64 : Nat) : Int) q2.toNat q3.toNat q4.toNat q5.toNat := by
    have : ((value t2 s3 s4 s5 + 2 ^ 256 * s6.toNat : Nat) : Int) = ((a.a2.toNat * value b.a0 b.a1 b.a2 b.a3 + value q2 q3 q4 q5 : Nat) : Int) := by rw [r2]
    simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, hw4] using this
  have ir3 : valI ((2 ^ 64 : Nat) : Int) t3.toNat t4.toNat t5.toNat t6.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * t7.toNat =
      a.a3.toNat * (value b.a0 b.a1 b.a2 b.a3 : Int) + valI ((2 ^ 64 : Nat) : Int) s3.toNat s4.toNat s5.toNat s6.toNat := by
    have : ((value t3 t4 t5 t6 + 2 ^ 256 * t7.toNat : Nat) : Int) = ((a.a3.toNat * value b.a0 b.a1 b.a2 b.a3 + value s3 s4 s5 s6 : Nat) : Int) := by rw [r3]
    simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, hw4] using this
  simp only [Sc.toNat, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul, valI_eq, hw4]
  exact mulWide4_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ir0 ir1 ir2 ir3

theorem c_words : Sc.c0.toNat + Sc.c1.toNat * 2 ^ 64 + 2 ^ 128 = 2 ^ 256 - N := by decide

private theorem fold1_alg (W c0 c1 L0 t4 t5 t6 t7 f0 u1 u2 u3 u4 f1 v2 v3 v4 v5 f2 k0 f3 k1 f4 k2 f5 f6 : Int)
    (r0 : valI W f0 u1 u2 u3 + W ^ 4 * u4 = c0 * valI W t4 t5 t6 t7 + L0)
    (r1 : valI W f1 v2 v3 v4 + W ^ 4 * v5 = c1 * valI W t4 t5 t6 t7 + valI W u1 u2 u3 u4)
    (a0 : f2 + k0 * W = v2 + t4)
    (a1 : f3 + k1 * W = v3 + t5 + k0)
    (a2 : f4 + k2 * W = v4 + t6 + k1)
    (a3 : f5 + f6 * W = v5 + t7 + k2) :
    valI W f0 f1 f2 f3 + W ^ 4 * valI W f4 f5 f6 0 =
      L0 + valI W t4 t5 t6 t7 * (c0 + c1 * W + W ^ 2) := by
  have hadc := adc4_alg W v2 v3 v4 v5 t4 t5 t6 t7 f2 k0 f3 k1 f4 k2 f5 f6 a0 a1 a2 a3
  rw [valI_shift] at r0 r1
  rw [valI_split2, hadc]
  clear a0 a1 a2 a3 hadc
  generalize valI W t4 t5 t6 t7 = H at r0 r1 ⊢
  generalize valI W u1 u2 u3 u4 = U1 at r0 r1
  generalize valI W v2 v3 v4 v5 = V2 at r1 ⊢
  grind

/-- First fold: `L0 + H0 · (2²⁵⁶ − N)` in seven words, with top 3 words `< 2¹³⁰`. -/
theorem fold1_spec (t0 t1 t2 t3 t4 t5 t6 t7 : UInt64) :
    let (f0, f1, f2, f3, f4, f5, f6) := Sc.fold1 t0 t1 t2 t3 t4 t5 t6 t7
    value f0 f1 f2 f3 + 2 ^ 256 * value f4 f5 f6 0 =
      value t0 t1 t2 t3 + value t4 t5 t6 t7 * (2 ^ 256 - N)
    ∧ value f4 f5 f6 0 < 2 ^ 130 := by
  simp only [Sc.fold1]
  have r0 := mulRow_spec Sc.c0 t4 t5 t6 t7 t0 t1 t2 t3
  rcases h0 : mulRow Sc.c0 t4 t5 t6 t7 t0 t1 t2 t3 with ⟨f0, u1, u2, u3, u4⟩
  rw [h0] at r0; clear h0; dsimp only at r0 ⊢
  have r1 := mulRow_spec Sc.c1 t4 t5 t6 t7 u1 u2 u3 u4
  rcases h1 : mulRow Sc.c1 t4 t5 t6 t7 u1 u2 u3 u4 with ⟨f1, v2, v3, v4, v5⟩
  rw [h1] at r1; clear h1; dsimp only at r1 ⊢
  obtain ⟨a0, hk0⟩ := adc_toNat v2 t4 0 (by decide)
  rcases ha0 : adc v2 t4 0 with ⟨f2, k0⟩; rw [ha0] at a0 hk0; clear ha0; dsimp only at a0 hk0 ⊢
  obtain ⟨a1, hk1⟩ := adc_toNat v3 t5 k0 hk0
  rcases ha1 : adc v3 t5 k0 with ⟨f3, k1⟩; rw [ha1] at a1 hk1; clear ha1; dsimp only at a1 hk1 ⊢
  obtain ⟨a2, hk2⟩ := adc_toNat v4 t6 k1 hk1
  rcases ha2 : adc v4 t6 k1 with ⟨f4, k2⟩; rw [ha2] at a2 hk2; clear ha2; dsimp only at a2 hk2 ⊢
  obtain ⟨a3, hk3⟩ := adc_toNat v5 t7 k2 hk2
  rcases ha3 : adc v5 t7 k2 with ⟨f5, f6⟩; rw [ha3] at a3 hk3; clear ha3; dsimp only at a3 hk3 ⊢
  simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero] at a0
  have eqv : value f0 f1 f2 f3 + 2 ^ 256 * value f4 f5 f6 0 =
      value t0 t1 t2 t3 + value t4 t5 t6 t7 * (2 ^ 256 - N) := by
    rw [← c_words]
    apply Int.ofNat.inj
    have p2 : (((2 ^ 128 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 2 := by decide
    have p4 : (((2 ^ 256 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 4 := by decide
    have ir0 : valI ((2 ^ 64 : Nat) : Int) f0.toNat u1.toNat u2.toNat u3.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * u4.toNat =
        Sc.c0.toNat * valI ((2 ^ 64 : Nat) : Int) t4.toNat t5.toNat t6.toNat t7.toNat + (value t0 t1 t2 t3 : Int) := by
      have : ((value f0 u1 u2 u3 + 2 ^ 256 * u4.toNat : Nat) : Int) = ((Sc.c0.toNat * value t4 t5 t6 t7 + value t0 t1 t2 t3 : Nat) : Int) := by rw [r0]
      simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, p4] using this
    have ir1 : valI ((2 ^ 64 : Nat) : Int) f1.toNat v2.toNat v3.toNat v4.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * v5.toNat =
        Sc.c1.toNat * valI ((2 ^ 64 : Nat) : Int) t4.toNat t5.toNat t6.toNat t7.toNat + valI ((2 ^ 64 : Nat) : Int) u1.toNat u2.toNat u3.toNat u4.toNat := by
      have : ((value f1 v2 v3 v4 + 2 ^ 256 * v5.toNat : Nat) : Int) = ((Sc.c1.toNat * value t4 t5 t6 t7 + value u1 u2 u3 u4 : Nat) : Int) := by rw [r1]
      simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, p4] using this
    have ia0 : (f2.toNat : Int) + k0.toNat * ((2 ^ 64 : Nat) : Int) = v2.toNat + t4.toNat := by exact_mod_cast a0
    have ia1 : (f3.toNat : Int) + k1.toNat * ((2 ^ 64 : Nat) : Int) = v3.toNat + t5.toNat + k0.toNat := by exact_mod_cast a1
    have ia2 : (f4.toNat : Int) + k2.toNat * ((2 ^ 64 : Nat) : Int) = v4.toNat + t6.toNat + k1.toNat := by exact_mod_cast a2
    have ia3 : (f5.toNat : Int) + f6.toNat * ((2 ^ 64 : Nat) : Int) = v5.toNat + t7.toNat + k2.toNat := by exact_mod_cast a3
    have h := fold1_alg ((2 ^ 64 : Nat) : Int) Sc.c0.toNat Sc.c1.toNat (value t0 t1 t2 t3) t4.toNat t5.toNat t6.toNat t7.toNat
      f0.toNat u1.toNat u2.toNat u3.toNat u4.toNat f1.toNat v2.toNat v3.toNat v4.toNat v5.toNat
      f2.toNat k0.toNat f3.toNat k1.toNat f4.toNat k2.toNat f5.toNat f6.toNat ir0 ir1 ia0 ia1 ia2 ia3
    have z0 : ((0 : UInt64).toNat : Int) = 0 := rfl
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul, valI_eq, z0, p2, p4]
    exact h
  have bL := value_lt t0 t1 t2 t3
  have bH := value_lt t4 t5 t6 t7
  have bLow := value_lt f0 f1 f2 f3
  refine ⟨eqv, ?_⟩
  clear r0 r1 a0 a1 a2 a3 hk0 hk1 hk2 hk3
  generalize value f0 f1 f2 f3 = FL at eqv bLow ⊢
  generalize value f4 f5 f6 0 = FH at eqv ⊢
  generalize value t0 t1 t2 t3 = L0 at eqv bL ⊢
  generalize value t4 t5 t6 t7 = H0 at eqv bH ⊢
  simp only [N, Nat.reducePow, Nat.reduceSub] at eqv bL bH bLow ⊢
  omega

private theorem fold2_alg (W c0 c1 L1 f4 f5 f6 g0 u1 u2 u3 u4 g1 v2 v3 v4 v5 g2 k0 g3 k1 g4 k2 : Int)
    (r0 : valI W g0 u1 u2 u3 + W ^ 4 * u4 = c0 * valI W f4 f5 f6 0 + L1)
    (r1 : valI W g1 v2 v3 v4 + W ^ 4 * v5 = c1 * valI W f4 f5 f6 0 + valI W u1 u2 u3 u4)
    (a0 : g2 + k0 * W = v2 + f4)
    (a1 : g3 + k1 * W = v3 + f5 + k0)
    (a2 : g4 + k2 * W = v4 + f6 + k1) :
    valI W g0 g1 g2 g3 + W ^ 4 * g4 + W ^ 5 * (v5 + k2) =
      L1 + valI W f4 f5 f6 0 * (c0 + c1 * W + W ^ 2) := by
  have a3 : (v5 + k2) + 0 * W = v5 + 0 + k2 := by omega
  have h := fold1_alg W c0 c1 L1 f4 f5 f6 0 g0 u1 u2 u3 u4 g1 v2 v3 v4 v5 g2 k0 g3 k1 g4 k2 (v5 + k2) 0 r0 r1 a0 a1 a2 a3
  have htop : valI W g0 g1 g2 g3 + W ^ 4 * g4 + W ^ 5 * (v5 + k2) =
      valI W g0 g1 g2 g3 + W ^ 4 * valI W g4 (v5 + k2) 0 0 := by
    generalize valI W g0 g1 g2 g3 = GL
    simp only [valI]; grind
  rw [htop, h]

/-- Second fold: `L1 + H1 · (2²⁵⁶ − N)` (for `H1 < 2¹³⁰`) fits in five words with top word `< 16`. -/
theorem fold2_spec (f0 f1 f2 f3 f4 f5 f6 : UInt64) (hH : value f4 f5 f6 0 < 2 ^ 130) :
    let (g0, g1, g2, g3, g4) := Sc.fold2 f0 f1 f2 f3 f4 f5 f6
    value g0 g1 g2 g3 + 2 ^ 256 * g4.toNat =
      value f0 f1 f2 f3 + value f4 f5 f6 0 * (2 ^ 256 - N)
    ∧ g4.toNat < 16 := by
  simp only [Sc.fold2]
  have r0 := mulRow_spec Sc.c0 f4 f5 f6 0 f0 f1 f2 f3
  rcases h0 : mulRow Sc.c0 f4 f5 f6 0 f0 f1 f2 f3 with ⟨g0, u1, u2, u3, u4⟩
  rw [h0] at r0; clear h0; dsimp only at r0 ⊢
  have r1 := mulRow_spec Sc.c1 f4 f5 f6 0 u1 u2 u3 u4
  rcases h1 : mulRow Sc.c1 f4 f5 f6 0 u1 u2 u3 u4 with ⟨g1, v2, v3, v4, v5⟩
  rw [h1] at r1; clear h1; dsimp only at r1 ⊢
  obtain ⟨a0, hk0⟩ := adc_toNat v2 f4 0 (by decide)
  rcases ha0 : adc v2 f4 0 with ⟨g2, k0⟩; rw [ha0] at a0 hk0; clear ha0; dsimp only at a0 hk0 ⊢
  obtain ⟨a1, hk1⟩ := adc_toNat v3 f5 k0 hk0
  rcases ha1 : adc v3 f5 k0 with ⟨g3, k1⟩; rw [ha1] at a1 hk1; clear ha1; dsimp only at a1 hk1 ⊢
  obtain ⟨a2, hk2⟩ := adc_toNat v4 f6 k1 hk1
  rcases ha2 : adc v4 f6 k1 with ⟨g4, k2⟩; rw [ha2] at a2 hk2; clear ha2; dsimp only at a2 hk2 ⊢
  simp only [show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero] at a0
  have eqFull : value g0 g1 g2 g3 + 2 ^ 256 * g4.toNat + 2 ^ 256 * 2 ^ 64 * (v5.toNat + k2.toNat) =
      value f0 f1 f2 f3 + value f4 f5 f6 0 * (2 ^ 256 - N) := by
    rw [← c_words]
    apply Int.ofNat.inj
    have p2 : (((2 ^ 128 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 2 := by decide
    have p4 : (((2 ^ 256 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 4 := by decide
    have p5 : (((2 ^ 64 : Nat) : Int)) ^ 4 * (((2 ^ 64 : Nat) : Int)) = (((2 ^ 64 : Nat) : Int)) ^ 5 := by decide
    have ir0 : valI ((2 ^ 64 : Nat) : Int) g0.toNat u1.toNat u2.toNat u3.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * u4.toNat =
        Sc.c0.toNat * valI ((2 ^ 64 : Nat) : Int) f4.toNat f5.toNat f6.toNat 0 + (value f0 f1 f2 f3 : Int) := by
      have : ((value g0 u1 u2 u3 + 2 ^ 256 * u4.toNat : Nat) : Int) = ((Sc.c0.toNat * value f4 f5 f6 0 + value f0 f1 f2 f3 : Nat) : Int) := by rw [r0]
      have z0 : ((0 : UInt64).toNat : Int) = 0 := rfl
      simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, z0, p4] using this
    have ir1 : valI ((2 ^ 64 : Nat) : Int) g1.toNat v2.toNat v3.toNat v4.toNat + ((2 ^ 64 : Nat) : Int) ^ 4 * v5.toNat =
        Sc.c1.toNat * valI ((2 ^ 64 : Nat) : Int) f4.toNat f5.toNat f6.toNat 0 + valI ((2 ^ 64 : Nat) : Int) u1.toNat u2.toNat u3.toNat u4.toNat := by
      have : ((value g1 v2 v3 v4 + 2 ^ 256 * v5.toNat : Nat) : Int) = ((Sc.c1.toNat * value f4 f5 f6 0 + value u1 u2 u3 u4 : Nat) : Int) := by rw [r1]
      have z0 : ((0 : UInt64).toNat : Int) = 0 := rfl
      simpa only [Int.natCast_add, Int.natCast_mul, valI_eq, z0, p4] using this
    have ia0 : (g2.toNat : Int) + k0.toNat * ((2 ^ 64 : Nat) : Int) = v2.toNat + f4.toNat := by exact_mod_cast a0
    have ia1 : (g3.toNat : Int) + k1.toNat * ((2 ^ 64 : Nat) : Int) = v3.toNat + f5.toNat + k0.toNat := by exact_mod_cast a1
    have ia2 : (g4.toNat : Int) + k2.toNat * ((2 ^ 64 : Nat) : Int) = v4.toNat + f6.toNat + k1.toNat := by exact_mod_cast a2
    have h := fold2_alg ((2 ^ 64 : Nat) : Int) Sc.c0.toNat Sc.c1.toNat (value f0 f1 f2 f3) f4.toNat f5.toNat f6.toNat
      g0.toNat u1.toNat u2.toNat u3.toNat u4.toNat g1.toNat v2.toNat v3.toNat v4.toNat v5.toNat
      g2.toNat k0.toNat g3.toNat k1.toNat g4.toNat k2.toNat ir0 ir1 ia0 ia1 ia2
    have z0 : ((0 : UInt64).toNat : Int) = 0 := rfl
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul, valI_eq, z0, p2, p4, p5] at h ⊢
    exact h
  have bL := value_lt f0 f1 f2 f3
  have bLow := value_lt g0 g1 g2 g3
  clear r0 r1 a0 a1 a2 hk0 hk1 hk2
  generalize value g0 g1 g2 g3 = GL at eqFull bLow ⊢
  generalize value f0 f1 f2 f3 = L1 at eqFull bL ⊢
  generalize value f4 f5 f6 0 = H1 at eqFull hH ⊢
  generalize g4.toNat = G4 at eqFull ⊢
  generalize v5.toNat + k2.toNat = Top at eqFull
  simp only [N, Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at eqFull bL bLow hH ⊢
  omega

/-- `a · b` modulo N, for any two scalars. -/
theorem Sc.mul_spec (a b : Sc) : (Sc.mul a b).toNat = (a.toNat * b.toNat) % N := by
  have hWide := mulWide4_spec a b
  rcases hw : Sc.mulWide4 a b with ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩
  rw [hw] at hWide; dsimp only at hWide
  have hF1 := fold1_spec t0 t1 t2 t3 t4 t5 t6 t7
  rcases hf1 : Sc.fold1 t0 t1 t2 t3 t4 t5 t6 t7 with ⟨f0, f1, f2, f3, f4, f5, f6⟩
  rw [hf1] at hF1; obtain ⟨vF1, bF1⟩ := hF1
  have hF2 := fold2_spec f0 f1 f2 f3 f4 f5 f6 bF1
  rcases hf2 : Sc.fold2 f0 f1 f2 f3 f4 f5 f6 with ⟨g0, g1, g2, g3, g4⟩
  rw [hf2] at hF2; obtain ⟨vF2, bG4⟩ := hF2
  have hF3 := mulRow_spec g4 Sc.c0 Sc.c1 1 0 g0 g1 g2 g3
  rcases hf3 : mulRow g4 Sc.c0 Sc.c1 1 0 g0 g1 g2 g3 with ⟨q0, q1, q2, q3, q4⟩
  rw [hf3] at hF3; dsimp only at hF3
  have cVal : value Sc.c0 Sc.c1 1 0 = 2 ^ 256 - N := by decide
  rw [cVal] at hF3
  have bL0 := value_lt t0 t1 t2 t3
  have bH0 := value_lt t4 t5 t6 t7
  have bL1 := value_lt f0 f1 f2 f3
  have bL2 := value_lt g0 g1 g2 g3
  have bQ := value_lt q0 q1 q2 q3
  have finish : q4.toNat ≤ 1 ∧ value q0 q1 q2 q3 + q4.toNat * 2 ^ 256 < 2 * N ∧
      a.toNat * b.toNat = value q0 q1 q2 q3 + q4.toNat * 2 ^ 256 +
        N * (value t4 t5 t6 t7 + value f4 f5 f6 0 + g4.toNat) := by
    generalize a.toNat * b.toNat = AB at hWide ⊢
    generalize value t0 t1 t2 t3 = L0 at hWide vF1 bL0
    generalize value t4 t5 t6 t7 = H0 at hWide vF1 bH0 ⊢
    generalize value f0 f1 f2 f3 = L1 at vF1 vF2 bL1
    generalize value f4 f5 f6 0 = H1 at vF1 vF2 bF1 ⊢
    generalize value g0 g1 g2 g3 = L2 at vF2 hF3 bL2
    generalize value q0 q1 q2 q3 = Q at hF3 bQ ⊢
    generalize g4.toNat = G4 at vF2 hF3 bG4 ⊢
    generalize q4.toNat = Q4 at hF3 ⊢
    clear hw hf1 hf2 hf3
    simp only [N, Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at hWide vF1 vF2 hF3 bL0 bH0 bL1 bL2 bQ bF1 bG4 ⊢
    omega
  obtain ⟨carry, small, whole⟩ := finish
  have reduced := reduceOnce_spec q0 q1 q2 q3 q4 carry small
  simp only [Sc.mul, hw, Sc.reduceWide, hf1, hf2, hf3]
  rw [reduced, whole, Nat.add_mul_mod_self_left]

/-- A product of scalars is below N whatever was multiplied. -/
theorem Sc.mul_lt (a b : Sc) : (Sc.mul a b).toNat < N := by
  rw [Sc.mul_spec]
  exact Nat.mod_lt _ (by decide)

end SecpCt
