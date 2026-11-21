import Secp.Curve.Spec

/-! # Unconditional primality of `P` and `N`, and Fermat's little theorem

Proved from first principles in pure Lean (`Nat`/`Int` only, no Mathlib, no axioms beyond the standard
three):

1. Bézout's identity and Euclid's lemma via the Euclidean algorithm (`bezout_int`, `coprime_dvd_of_dvd_mul`).
2. Fermat's little theorem (`fermat_of_prime`) via Pascal's identity `k · C(p, k) = p · C(p − 1, k − 1)` and
   induction on `a` (`(a + 1)^p ≡ a^p + 1 (mod p)`).
3. Squarefree Pocklington's criterion (`prime_of_pocklington`): if distinct primes `qs` divide `n − 1` with
   `(∏ qs)² > n`, `a^(n − 1) ≡ 1 (mod n)`, and `gcd(a^((n − 1)/q) − 1, n) = 1` for each `q ∈ qs`, then any
   prime factor `p ≤ √n` of `n` satisfies `q ∣ (p − 1)` for every `q ∈ qs` (by Fermat for `p` and Bézout),
   giving `∏ qs ≤ p − 1 < √n`, a contradiction.
4. A 29-step Pocklington DAG down to seven small primes certifies both the field prime `Secp.P` and the
   group order `Secp.Spec.N`, instantiating `Secp.Spec.FieldP` unconditionally. -/

namespace Secp.Primes

/-- `p` is prime: at least 2, with only 1 and `p` as divisors. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Every integer `≥ 2` has a prime divisor. -/
theorem exists_prime_dvd : ∀ {n : Nat}, 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hp : ∀ d, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hp⟩, Nat.dvd_refl n⟩
    · simp only [Classical.not_forall, not_or] at hp
      obtain ⟨d, hd, hne1, hnen⟩ := hp
      have hd0 : d ≠ 0 := by intro h0; subst h0; obtain ⟨k, hk⟩ := hd; omega
      have hle : d ≤ n := Nat.le_of_dvd (by omega) hd
      obtain ⟨p, hprime, hpd⟩ := ih d (by omega) (by omega)
      exact ⟨p, hprime, Nat.dvd_trans hpd hd⟩

/-- Every composite integer `≥ 2` has a prime divisor `p` with `p² ≤ n`. -/
theorem composite_prime_le_sq {n : Nat} (hn : 2 ≤ n) (hnot : ¬ IsPrime n) :
    ∃ p, IsPrime p ∧ p ∣ n ∧ p * p ≤ n := by
  have hex : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
    by_cases h : ∀ d, d ∣ n → d = 1 ∨ d = n
    · exact absurd ⟨hn, h⟩ hnot
    · simp only [Classical.not_forall, not_or] at h
      obtain ⟨d, hd, h1, hn'⟩ := h
      exact ⟨d, hd, h1, hn'⟩
  obtain ⟨d, ⟨q, hnq⟩, hd1, hdn⟩ := hex
  have hd2 : 2 ≤ d := by
    by_cases h0 : d = 0
    · subst h0; omega
    · omega
  have hq2 : 2 ≤ q := by
    by_cases hq0 : q = 0
    · subst hq0; omega
    · by_cases hq1 : q = 1
      · subst hq1; simp at hnq; exact absurd hnq.symm hdn
      · omega
  have ⟨m, hm2, hmdvd, hmsq⟩ : ∃ m, 2 ≤ m ∧ m ∣ n ∧ m * m ≤ n := by
    by_cases hle : d ≤ q
    · refine ⟨d, hd2, ⟨q, hnq⟩, ?_⟩
      calc d * d ≤ d * q := Nat.mul_le_mul_left d hle
        _ = n := hnq.symm
    · refine ⟨q, hq2, ⟨d, by rw [Nat.mul_comm]; exact hnq⟩, ?_⟩
      calc q * q ≤ d * q := Nat.mul_le_mul_right q (by omega)
        _ = n := hnq.symm
  obtain ⟨p, hp, hpm⟩ := exists_prime_dvd hm2
  have hple : p ≤ m := Nat.le_of_dvd (by omega) hpm
  refine ⟨p, hp, Nat.dvd_trans hpm hmdvd, ?_⟩
  calc p * p ≤ m * m := Nat.mul_le_mul hple hple
    _ ≤ n := hmsq

/-- Trial division certificate for small leaf primes. -/
def checkSmallPrime (p : Nat) : Bool :=
  2 ≤ p && (List.range' 2 (p - 2)).all (fun d => p % d != 0)

theorem prime_of_checkSmallPrime {p : Nat} (h : checkSmallPrime p = true) : IsPrime p := by
  simp only [checkSmallPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hp2, hall⟩ := h
  refine ⟨hp2, fun d hd => ?_⟩
  have hd0 : d ≠ 0 := by intro h0; subst h0; obtain ⟨k, hk⟩ := hd; omega
  have hdle : d ≤ p := Nat.le_of_dvd (by omega) hd
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · by_cases hdp : d = p
    · exact Or.inr hdp
    · exfalso
      have hmem : d ∈ List.range' 2 (p - 2) := List.mem_range'.mpr ⟨d - 2, by omega, by omega⟩
      exact hall d hmem (Nat.mod_eq_zero_of_dvd hd)

/-! ## Bézout and Euclid's lemma -/

theorem bezout_int : ∀ a b : Nat, ∃ x y : Int, x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b
    by_cases ha : a = 0
    · subst ha
      exact ⟨0, 1, by simp⟩
    · have hlt : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero ha)
      obtain ⟨x, y, hxy⟩ := ih (b % a) hlt a
      have hdiv : (b % a : Int) + (a : Int) * (b / a : Int) = (b : Int) := by
        exact_mod_cast Nat.mod_add_div b a
      refine ⟨y - x * (b / a : Int), x, ?_⟩
      rw [Nat.gcd_rec a b, ← hxy]
      grind

theorem nonneg_of_mul_nonneg_left {a : Int} {w : Int} (ha : 0 < a) (h : 0 ≤ a * w) : 0 ≤ w := by
  by_cases hw : 0 ≤ w
  · exact hw
  · exfalso
    have hw1 : w + 1 ≤ 0 := by omega
    have hm : a * (w + 1) ≤ a * 0 := Int.mul_le_mul_of_nonneg_left hw1 (by omega)
    have : a * w + a ≤ 0 := by grind
    omega

theorem coprime_dvd_of_dvd_mul {a b c : Nat} (hg : Nat.gcd a b = 1) (hd : a ∣ b * c) : a ∣ c := by
  by_cases ha : a = 0
  · subst ha
    simp only [Nat.gcd_zero_left] at hg
    subst hg
    simpa using hd
  · obtain ⟨k, hk⟩ := hd
    obtain ⟨x, y, hxy⟩ := bezout_int a b
    rw [hg] at hxy
    let w : Int := x * (c : Int) + y * (k : Int)
    have hcw : (c : Int) = (a : Int) * w := by
      have hbc : (b : Int) * (c : Int) = (a : Int) * (k : Int) := by exact_mod_cast hk
      calc (c : Int) = (x * (a : Int) + y * (b : Int)) * (c : Int) := by rw [hxy]; simp
        _ = (a : Int) * (x * (c : Int)) + y * ((b : Int) * (c : Int)) := by grind
        _ = (a : Int) * w := by rw [hbc]; grind
    have ha_pos : (0 : Int) < (a : Int) := by omega
    have hcw_nonneg : (0 : Int) ≤ (a : Int) * w := by rw [← hcw]; exact Int.natCast_nonneg c
    have hw0 : 0 ≤ w := nonneg_of_mul_nonneg_left ha_pos hcw_nonneg
    refine ⟨w.toNat, ?_⟩
    have hwn : (w.toNat : Int) = w := Int.toNat_of_nonneg hw0
    have : (c : Int) = ((a * w.toNat : Nat) : Int) := by simp [Int.natCast_mul, hwn, hcw]
    exact Int.ofNat.inj this

theorem prime_coprime_of_not_dvd {p a : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ a) : Nat.gcd p a = 1 := by
  rcases hp.2 _ (Nat.gcd_dvd_left p a) with h1 | hp'
  · exact h1
  · exfalso
    have hda := Nat.gcd_dvd_right p a
    rw [hp'] at hda
    exact hnd hda

theorem bezout_pos {a b : Nat} (hg : Nat.gcd a b = 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ u v : Nat, u * a = 1 + v * b := by
  obtain ⟨x, y, hxy⟩ := bezout_int a b
  rw [hg] at hxy
  let m : Int := if 0 < x then 0 else 1 - x
  let x' : Int := x + m * (b : Int)
  let y' : Int := -(y - m * (a : Int))
  have hx' : 0 < x' := by
    dsimp [x', m]
    split
    · omega
    · have : 1 - x > 0 := by omega
      have hbm : (1 - x) * 1 ≤ (1 - x) * (b : Int) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  have heq : x' * (a : Int) - 1 = (b : Int) * y' := by
    dsimp [x', y']
    grind
  have hy'0 : 0 ≤ y' := by
    have : 1 ≤ x' * (a : Int) := by
      have : 1 * 1 ≤ x' * (a : Int) := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      omega
    exact nonneg_of_mul_nonneg_left (a := (b : Int)) (w := y') (by omega) (by rw [← heq]; omega)
  refine ⟨x'.toNat, y'.toNat, ?_⟩
  have hxn : (x'.toNat : Int) = x' := Int.toNat_of_nonneg (by omega)
  have hyn : (y'.toNat : Int) = y' := Int.toNat_of_nonneg hy'0
  have : ((x'.toNat * a : Nat) : Int) = ((1 + y'.toNat * b : Nat) : Int) := by
    simp only [Int.natCast_mul, Int.natCast_add, hxn, hyn]
    grind
  exact Int.ofNat.inj this

/-! ## Fermat's little theorem -/

def binom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_zero_right : ∀ n, binom n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem binom_gt : ∀ n k, n < k → binom n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    simp only [binom]
    rw [binom_gt n k (by omega), binom_gt n (k + 1) (by omega)]

theorem binom_self : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by simp only [binom, binom_self n, binom_gt n (n + 1) (by omega), Nat.add_zero]

theorem mul_binom : ∀ n k, (k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k
  | 0, 0 => rfl
  | 0, k + 1 => by simp [binom]
  | n + 1, 0 => by
    have ih := mul_binom n 0
    simp only [binom, binom_zero_right, Nat.mul_one] at ih ⊢
    omega
  | n + 1, k + 1 => by
    have h1 := mul_binom n k
    have h2 := mul_binom n (k + 1)
    have lhs : (k + 2) * binom (n + 2) (k + 2) =
        (k + 1) * binom (n + 1) (k + 1) + binom (n + 1) (k + 1) + (k + 2) * binom (n + 1) (k + 2) := by
      change (k + 2) * (binom (n + 1) (k + 1) + binom (n + 1) (k + 2)) = _
      rw [Nat.mul_add, show (k + 2) * binom (n + 1) (k + 1) = (k + 1) * binom (n + 1) (k + 1) + binom (n + 1) (k + 1) by
        rw [show k + 2 = (k + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]]
    rw [lhs, h1, h2]
    have rhs : (n + 2) * binom (n + 1) (k + 1) = (n + 1) * binom n k + binom (n + 1) (k + 1) + (n + 1) * binom n (k + 1) := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      conv => lhs; arg 1; rw [show binom (n + 1) (k + 1) = binom n k + binom n (k + 1) from rfl, Nat.mul_add]
      omega
    rw [rhs]

theorem prime_dvd_binom {p k : Nat} (hp : IsPrime p) (hk1 : 1 ≤ k) (hkp : k < p) : p ∣ binom p k := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hm := mul_binom p' k'
  have hdvd : (p' + 1) ∣ (k' + 1) * binom (p' + 1) (k' + 1) := ⟨binom p' k', hm⟩
  have hnd : ¬ (p' + 1) ∣ (k' + 1) := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  exact coprime_dvd_of_dvd_mul (prime_coprime_of_not_dvd hp hnd) hdvd

def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumRange f m + f m

theorem sumRange_add (f g : Nat → Nat) (m : Nat) :
    sumRange (fun k => f k + g k) m = sumRange f m + sumRange g m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sumRange, ih]; omega

theorem sumRange_succ_shift (f : Nat → Nat) : ∀ m : Nat,
    sumRange f (m + 1) = f 0 + sumRange (fun k => f (k + 1)) m
  | 0 => by simp [sumRange]
  | m + 1 => by
    calc sumRange f (m + 2) = sumRange f (m + 1) + f (m + 1) := rfl
      _ = (f 0 + sumRange (fun k => f (k + 1)) m) + f (m + 1) := by rw [sumRange_succ_shift f m]
      _ = f 0 + sumRange (fun k => f (k + 1)) (m + 1) := by simp only [sumRange]; omega

theorem add_one_pow (a : Nat) : ∀ n : Nat, (a + 1) ^ n = sumRange (fun k => binom n k * a ^ k) (n + 1)
  | 0 => by simp [sumRange, binom]
  | n + 1 => by
    rw [Nat.pow_succ, add_one_pow a n]
    have hmul : ∀ m, sumRange (fun k => binom n k * a ^ k) m * (a + 1) =
        sumRange (fun k => binom n k * a ^ (k + 1)) m + sumRange (fun k => binom n k * a ^ k) m := by
      intro m
      induction m with
      | zero => simp [sumRange]
      | succ m ih => simp only [sumRange, Nat.add_mul, ih, Nat.pow_succ]; grind
    rw [hmul (n + 1)]
    have s1 : sumRange (fun k => binom n k * a ^ (k + 1)) (n + 1) =
        sumRange (fun k => binom n k * a ^ (k + 1)) n + a ^ (n + 1) := by
      simp only [sumRange, binom_self n, Nat.one_mul]
    have s2 : sumRange (fun k => binom n k * a ^ k) (n + 1) =
        1 + sumRange (fun k => binom n (k + 1) * a ^ (k + 1)) n := by
      rw [sumRange_succ_shift (fun k => binom n k * a ^ k) n, binom_zero_right, Nat.pow_zero, Nat.one_mul]
    have s3 : sumRange (fun k => binom (n + 1) k * a ^ k) (n + 2) =
        1 + sumRange (fun k => binom (n + 1) (k + 1) * a ^ (k + 1)) n + a ^ (n + 1) := by
      calc sumRange (fun k => binom (n + 1) k * a ^ k) (n + 2)
          = sumRange (fun k => binom (n + 1) k * a ^ k) (n + 1) + binom (n + 1) (n + 1) * a ^ (n + 1) := rfl
        _ = 1 + sumRange (fun k => binom (n + 1) (k + 1) * a ^ (k + 1)) n + a ^ (n + 1) := by
          rw [sumRange_succ_shift (fun k => binom (n + 1) k * a ^ k) n, binom_zero_right, binom_self,
              Nat.pow_zero, Nat.one_mul, Nat.one_mul]
    have hbody : sumRange (fun k => binom (n + 1) (k + 1) * a ^ (k + 1)) n =
        sumRange (fun k => binom n k * a ^ (k + 1)) n + sumRange (fun k => binom n (k + 1) * a ^ (k + 1)) n := by
      rw [← sumRange_add]
      congr 1; funext k; simp only [binom, Nat.add_mul]
    rw [s1, s2, s3, hbody]
    omega

theorem dvd_sumRange {p : Nat} (f : Nat → Nat) : ∀ m, (∀ k < m, p ∣ f k) → p ∣ sumRange f m
  | 0, _ => ⟨0, by simp [sumRange]⟩
  | m + 1, h => by
    simp only [sumRange]
    exact Nat.dvd_add (dvd_sumRange f m (fun k hk => h k (by omega))) (h m (by omega))

theorem add_one_pow_mod_prime {p : Nat} (hp : IsPrime p) (a : Nat) :
    (a + 1) ^ p % p = (a ^ p + 1) % p := by
  have hp2 := hp.1
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hexp : (a + 1) ^ (m + 1) = 1 + sumRange (fun k => binom (m + 1) (k + 1) * a ^ (k + 1)) m + a ^ (m + 1) := by
    rw [add_one_pow a (m + 1)]
    calc sumRange (fun k => binom (m + 1) k * a ^ k) (m + 2)
        = sumRange (fun k => binom (m + 1) k * a ^ k) (m + 1) + binom (m + 1) (m + 1) * a ^ (m + 1) := rfl
      _ = 1 + sumRange (fun k => binom (m + 1) (k + 1) * a ^ (k + 1)) m + a ^ (m + 1) := by
        rw [binom_self (m + 1), Nat.one_mul, sumRange_succ_shift (fun k => binom (m + 1) k * a ^ k) m,
            binom_zero_right, Nat.pow_zero, Nat.one_mul]
  rw [hexp]
  have hdvd : (m + 1) ∣ sumRange (fun k => binom (m + 1) (k + 1) * a ^ (k + 1)) m := by
    apply dvd_sumRange
    intro k hk
    exact Nat.dvd_mul_right_of_dvd (prime_dvd_binom hp (by omega) (by omega)) _
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, show 1 + (m + 1) * q + a ^ (m + 1) = a ^ (m + 1) + 1 + (m + 1) * q by omega,
      Nat.add_mul_mod_self_left]

theorem pow_prime_mod {p : Nat} (hp : IsPrime p) : ∀ a : Nat, a ^ p % p = a % p
  | 0 => by
    have hp2 := hp.1
    have hpos : 0 < p := by omega
    rw [Nat.zero_pow hpos]
  | a + 1 => by
    rw [add_one_pow_mod_prime hp a, ← Nat.mod_add_mod, pow_prime_mod hp a, Nat.mod_add_mod]

theorem fermat_of_prime {p : Nat} (hp : IsPrime p) (a : Nat) (ha : a % p ≠ 0) :
    a ^ (p - 1) % p = 1 := by
  have hp2 := hp.1
  have ha0 : 0 < a := by
    by_cases h : a = 0
    · subst h; simp at ha
    · omega
  have hpow : a ^ p = a * a ^ (p - 1) := by
    conv => lhs; rw [show p = p - 1 + 1 by omega, Nat.pow_succ']
  have hge1 : 1 ≤ a ^ (p - 1) := Nat.one_le_pow _ _ ha0
  have hmod := pow_prime_mod hp a
  rw [hpow] at hmod
  have hdvd_diff : p ∣ a * (a ^ (p - 1) - 1) := by
    have hmul_ge : a ≤ a * a ^ (p - 1) := by
      calc a = a * 1 := (Nat.mul_one a).symm
        _ ≤ a * a ^ (p - 1) := Nat.mul_le_mul_left a hge1
    have hsub : a * (a ^ (p - 1) - 1) = a * a ^ (p - 1) - a := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [hsub, Nat.dvd_iff_mod_eq_zero]
    have d1 := Nat.div_add_mod (a * a ^ (p - 1)) p
    have d2 := Nat.div_add_mod a p
    rw [hmod] at d1
    have hle_div : a / p ≤ a * a ^ (p - 1) / p := Nat.div_le_div_right hmul_ge
    have : a * a ^ (p - 1) - a = p * (a * a ^ (p - 1) / p - a / p) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [this, Nat.mul_mod_right]
  have hnd : ¬ p ∣ a := fun h => ha (Nat.mod_eq_zero_of_dvd h)
  obtain ⟨k, hk⟩ := coprime_dvd_of_dvd_mul (prime_coprime_of_not_dvd hp hnd) hdvd_diff
  have : a ^ (p - 1) = 1 + p * k := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp2]

/-! ## Squarefree Pocklington certificates -/

def powMod (b e m : Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let r := powMod b (e / 2) m
    let r2 := r * r % m
    if e % 2 = 1 then r2 * b % m else r2

theorem powMod_eq (b : Nat) : ∀ e m : Nat, powMod b e m = b ^ e % m := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro m
    unfold powMod
    by_cases he : e = 0
    · simp [he]
    · simp only [he, ↓reduceIte]
      rw [ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)) m]
      have hdiv : 2 * (e / 2) + e % 2 = e := Nat.div_add_mod e 2
      have hsq : b ^ (e / 2) % m * (b ^ (e / 2) % m) % m = b ^ (2 * (e / 2)) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add, Nat.two_mul]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, ↓reduceIte]
        rw [hsq, Nat.mod_mul_mod, ← Nat.pow_succ, show (2 * (e / 2)).succ = e by omega]
      · simp only [hodd, ↓reduceIte, hsq, show 2 * (e / 2) = e by omega]

def prodList : List Nat → Nat
  | [] => 1
  | q :: qs => q * prodList qs

def pairwiseGt : List Nat → Bool
  | [] => true
  | q :: qs => qs.all (q > ·) && pairwiseGt qs

def checkPocklington (n a : Nat) (qs : List Nat) : Bool :=
  2 ≤ n && pairwiseGt qs && (n - 1) % prodList qs == 0 && prodList qs * prodList qs > n &&
  powMod a (n - 1) n == 1 &&
  qs.all (fun q => q > 0 && Nat.gcd (powMod a ((n - 1) / q) n + n - 1) n == 1)

theorem mem_dvd_prodList {q : Nat} : ∀ {qs : List Nat}, q ∈ qs → q ∣ prodList qs
  | [], h => nomatch h
  | x :: xs, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | hm
    · exact ⟨prodList xs, rfl⟩
    · obtain ⟨k, hk⟩ := mem_dvd_prodList hm
      exact ⟨x * k, by simp only [prodList, hk]; grind⟩

theorem prime_not_dvd_prodList {q : Nat} (hq : IsPrime q) :
    ∀ {qs : List Nat}, (∀ r ∈ qs, IsPrime r) → (∀ r ∈ qs, r < q) → ¬ q ∣ prodList qs
  | [], _, _, hd => by
    simp only [prodList] at hd
    have := Nat.le_of_dvd (by decide) hd
    exact absurd this (by have := hq.1; omega)
  | r :: rs, hpr, hlt, hd => by
    simp only [prodList] at hd
    have hr_lt : r < q := hlt r List.mem_cons_self
    have hnd_r : ¬ q ∣ r := by
      intro h
      have := Nat.le_of_dvd (by have := (hpr r List.mem_cons_self).1; omega) h
      omega
    have hd_rs := coprime_dvd_of_dvd_mul (prime_coprime_of_not_dvd hq hnd_r) hd
    exact prime_not_dvd_prodList hq (fun x hx => hpr x (List.mem_cons_of_mem _ hx))
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) hd_rs

theorem prodList_dvd_of_all {m : Nat} :
    ∀ {qs : List Nat}, pairwiseGt qs = true → (∀ q ∈ qs, IsPrime q) → (∀ q ∈ qs, q ∣ m) → prodList qs ∣ m
  | [], _, _, _ => Nat.one_dvd m
  | q :: qs, hpw, hpr, hdvd => by
    simp only [pairwiseGt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hpw
    have hq : IsPrime q := hpr q List.mem_cons_self
    have h_rest : prodList qs ∣ m :=
      prodList_dvd_of_all hpw.2 (fun r hr => hpr r (List.mem_cons_of_mem _ hr))
        (fun r hr => hdvd r (List.mem_cons_of_mem _ hr))
    obtain ⟨k, hk⟩ := h_rest
    have hqd : q ∣ prodList qs * k := hk ▸ hdvd q List.mem_cons_self
    have hnd : ¬ q ∣ prodList qs :=
      prime_not_dvd_prodList hq (fun r hr => hpr r (List.mem_cons_of_mem _ hr)) (fun r hr => hpw.1 r hr)
    obtain ⟨t, ht⟩ := coprime_dvd_of_dvd_mul (prime_coprime_of_not_dvd hq hnd) hqd
    exact ⟨t, by simp only [prodList, hk, ht]; grind⟩

theorem pow_mod_one {b e p : Nat} (h : b % p = 1) (hp : 2 ≤ p) : b ^ e % p = 1 := by
  induction e with
  | zero => exact Nat.mod_eq_of_lt hp
  | succ e ih => rw [Nat.pow_succ, Nat.mul_mod, ih, h, Nat.one_mul, Nat.mod_eq_of_lt hp]

theorem prime_of_pocklington {n a : Nat} {qs : List Nat}
    (hpr : ∀ q ∈ qs, IsPrime q) (hchk : checkPocklington n a qs = true) : IsPrime n := by
  simp only [checkPocklington, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨hn2, hpw⟩, hF_mod⟩, hF_sq⟩, ha_pow⟩, hall_q⟩ := hchk
  rw [powMod_eq] at ha_pow
  by_cases his : IsPrime n
  · exact his
  · exfalso
    obtain ⟨p, hp, hpn, hpsq⟩ := composite_prime_le_sq hn2 his
    have hp2 := hp.1
    have ha_mod_p : a ^ (n - 1) % p = 1 := by
      obtain ⟨c, hnc⟩ := hpn
      have d := Nat.div_add_mod (a ^ (n - 1)) (p * c)
      rw [← hnc, ha_pow, hnc] at d
      have : a ^ (n - 1) = 1 + p * (c * (a ^ (n - 1) / (p * c))) := by grind
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp2]
    have ha_nz : a % p ≠ 0 := by
      intro hz
      obtain ⟨k, hk⟩ : ∃ k, n - 1 = k + 1 := ⟨n - 2, by omega⟩
      rw [hk, Nat.pow_succ, Nat.mul_mod, hz, Nat.mul_zero, Nat.zero_mod] at ha_mod_p
      omega
    have hq_dvd : ∀ q ∈ qs, q ∣ (p - 1) := by
      intro q hq_mem
      have hqi := hpr q hq_mem
      have ⟨_, hgcd⟩ := hall_q q hq_mem
      rw [powMod_eq] at hgcd
      have hq_dvd_n1 : q ∣ (n - 1) :=
        Nat.dvd_trans (mem_dvd_prodList hq_mem) (Nat.dvd_of_mod_eq_zero hF_mod)
      let m := (n - 1) / q
      have hqm : q * m = n - 1 := Nat.mul_div_cancel' hq_dvd_n1
      have ham_ne1 : a ^ m % p ≠ 1 := by
        intro ham1
        obtain ⟨c, hnc⟩ := hpn
        have r_lt : a ^ m % (p * c) < p * c := Nat.mod_lt _ (by omega)
        have r_mod_p : (a ^ m % (p * c)) % p = 1 := by
          have d := Nat.div_add_mod (a ^ m) (p * c)
          have : a ^ m = a ^ m % (p * c) + p * (c * (a ^ m / (p * c))) := by grind
          rw [this, Nat.add_mul_mod_self_left] at ham1
          exact ham1
        have hp_dvd_val : p ∣ (a ^ m % (p * c) + p * c - 1) := by
          have hr1 : 1 ≤ a ^ m % (p * c) := by
            by_cases h0 : a ^ m % (p * c) = 0
            · rw [h0, Nat.zero_mod] at r_mod_p; omega
            · omega
          have hsplit : a ^ m % (p * c) + p * c - 1 = (a ^ m % (p * c) - 1) + p * c := by omega
          rw [hsplit]
          apply Nat.dvd_add _ ⟨c, rfl⟩
          have hd := Nat.div_add_mod (a ^ m % (p * c)) p
          rw [r_mod_p] at hd
          exact ⟨a ^ m % (p * c) / p, by omega⟩
        have hp_dvd_gcd : p ∣ Nat.gcd (a ^ m % (p * c) + p * c - 1) (p * c) :=
          Nat.dvd_gcd hp_dvd_val ⟨c, rfl⟩
        rw [← hnc] at hp_dvd_gcd
        change p ∣ Nat.gcd (a ^ ((n - 1) / q) % n + n - 1) n at hp_dvd_gcd
        rw [hgcd] at hp_dvd_gcd
        have := Nat.le_of_dvd (by decide) hp_dvd_gcd
        omega
      by_cases hqp : q ∣ (p - 1)
      · exact hqp
      · exfalso
        have hcop := prime_coprime_of_not_dvd hqi hqp
        obtain ⟨u, v, huv⟩ := bezout_pos hcop (by have := hqi.1; omega) (by omega)
        have lhs : (a ^ m) ^ (u * q) % p = 1 := by
          rw [Nat.mul_comm u q, ← Nat.pow_mul, ← Nat.mul_assoc, Nat.mul_comm m q, hqm, Nat.pow_mul]
          exact pow_mod_one ha_mod_p hp2
        have rhs : (a ^ m) ^ (1 + v * (p - 1)) % p = a ^ m % p := by
          rw [Nat.pow_add, Nat.pow_one, ← Nat.pow_mul, show m * (v * (p - 1)) = (p - 1) * (m * v) by grind,
              Nat.pow_mul]
          have hf := fermat_of_prime hp a ha_nz
          have h1 := pow_mod_one hf hp2 (e := m * v)
          rw [Nat.mul_mod, h1, Nat.mul_one, Nat.mod_mod]
        rw [huv] at lhs
        exact ham_ne1 (rhs.symm.trans lhs)
    have hF_dvd : prodList qs ∣ (p - 1) := prodList_dvd_of_all hpw hpr hq_dvd
    have hF_le : prodList qs ≤ p - 1 := Nat.le_of_dvd (by omega) hF_dvd
    have hsq_le : prodList qs * prodList qs ≤ (p - 1) * (p - 1) := Nat.mul_le_mul hF_le hF_le
    have hlt_sq : (p - 1) * (p - 1) < p * p := by
      have : (p - 1) * (p - 1) < p * (p - 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      have : p * (p - 1) ≤ p * p := Nat.mul_le_mul_left p (by omega)
      omega
    omega

/-! ## The certificate DAG for `Secp.P` and `Secp.Spec.N` -/

private theorem p_2 : IsPrime 2 := prime_of_checkSmallPrime (by decide +kernel)
private theorem p_3 : IsPrime 3 := prime_of_checkSmallPrime (by decide +kernel)
private theorem p_5 : IsPrime 5 := prime_of_checkSmallPrime (by decide +kernel)
private theorem p_7 : IsPrime 7 := prime_of_checkSmallPrime (by decide +kernel)
private theorem p_17 : IsPrime 17 := prime_of_checkSmallPrime (by decide +kernel)
private theorem p_101 : IsPrime 101 := prime_of_checkSmallPrime (by decide +kernel)
private theorem p_1409 : IsPrime 1409 := prime_of_checkSmallPrime (by decide +kernel)

private theorem all_1 {P : Nat → Prop} {a : Nat} (ha : P a) : ∀ q ∈ [a], P q := by
  intro q h; simp at h; subst h; exact ha
private theorem all_2 {P : Nat → Prop} {a b : Nat} (ha : P a) (hb : P b) : ∀ q ∈ [a, b], P q := by
  intro q h; simp at h; rcases h with rfl | rfl <;> assumption
private theorem all_3 {P : Nat → Prop} {a b c : Nat} (ha : P a) (hb : P b) (hc : P c) :
    ∀ q ∈ [a, b, c], P q := by
  intro q h; simp at h; rcases h with rfl | rfl | rfl <;> assumption

private theorem p_11 : IsPrime 11 :=
  prime_of_pocklington (a := 2) (all_1 p_5) (by decide +kernel)
private theorem p_13 : IsPrime 13 :=
  prime_of_pocklington (a := 2) (all_2 p_3 p_2) (by decide +kernel)
private theorem p_19 : IsPrime 19 :=
  prime_of_pocklington (a := 2) (all_2 p_3 p_2) (by decide +kernel)
private theorem p_29 : IsPrime 29 :=
  prime_of_pocklington (a := 2) (all_1 p_7) (by decide +kernel)
private theorem p_41 : IsPrime 41 :=
  prime_of_pocklington (a := 6) (all_2 p_5 p_2) (by decide +kernel)
private theorem p_53 : IsPrime 53 :=
  prime_of_pocklington (a := 2) (all_1 p_13) (by decide +kernel)
private theorem p_113 : IsPrime 113 :=
  prime_of_pocklington (a := 3) (all_2 p_7 p_2) (by decide +kernel)
private theorem p_239 : IsPrime 239 :=
  prime_of_pocklington (a := 2) (all_1 p_17) (by decide +kernel)
private theorem p_419 : IsPrime 419 :=
  prime_of_pocklington (a := 2) (all_2 p_19 p_11) (by decide +kernel)
private theorem p_1871 : IsPrime 1871 :=
  prime_of_pocklington (a := 2) (all_2 p_17 p_11) (by decide +kernel)
private theorem p_9349 : IsPrime 9349 :=
  prime_of_pocklington (a := 2) (all_2 p_41 p_19) (by decide +kernel)
private theorem p_20113 : IsPrime 20113 :=
  prime_of_pocklington (a := 2) (all_1 p_419) (by decide +kernel)
private theorem p_28181 : IsPrime 28181 :=
  prime_of_pocklington (a := 2) (all_1 p_1409) (by decide +kernel)
private theorem p_96557 : IsPrime 96557 :=
  prime_of_pocklington (a := 2) (all_2 p_239 p_101) (by decide +kernel)
private theorem p_120233 : IsPrime 120233 :=
  prime_of_pocklington (a := 2) (all_2 p_113 p_19) (by decide +kernel)
private theorem p_1206781 : IsPrime 1206781 :=
  prime_of_pocklington (a := 2) (all_1 p_20113) (by decide +kernel)
private theorem p_1627771 : IsPrime 1627771 :=
  prime_of_pocklington (a := 2) (all_1 p_1871) (by decide +kernel)
private theorem p_7240687 : IsPrime 7240687 :=
  prime_of_pocklington (a := 2) (all_1 p_1206781) (by decide +kernel)
private theorem p_44706919 : IsPrime 44706919 :=
  prime_of_pocklington (a := 2) (all_1 p_9349) (by decide +kernel)
private theorem p_107590001 : IsPrime 107590001 :=
  prime_of_pocklington (a := 2) (all_3 p_53 p_29 p_7) (by decide +kernel)
private theorem p_545358713 : IsPrime 545358713 :=
  prime_of_pocklington (a := 2) (all_1 p_28181) (by decide +kernel)
private theorem p_297159362677 : IsPrime 297159362677 :=
  prime_of_pocklington (a := 2) (all_1 p_1627771) (by decide +kernel)
private theorem p_174723607534414371449 : IsPrime 174723607534414371449 :=
  prime_of_pocklington (a := 2) (all_2 p_44706919 p_120233) (by decide +kernel)
private theorem p_29047611873442575647497758179 : IsPrime 29047611873442575647497758179 :=
  prime_of_pocklington (a := 2) (all_2 p_297159362677 p_545358713) (by decide +kernel)
private theorem p_341948486974166000522343609283189 : IsPrime 341948486974166000522343609283189 :=
  prime_of_pocklington (a := 2) (all_1 p_29047611873442575647497758179) (by decide +kernel)
private theorem p_255515944373312847190720520512484175977 :
    IsPrime 255515944373312847190720520512484175977 :=
  prime_of_pocklington (a := 2) (all_3 p_107590001 p_7240687 p_96557) (by decide +kernel)
private theorem p_205115282021455665897114700593932402728804164701536103180137503955397371 :
    IsPrime 205115282021455665897114700593932402728804164701536103180137503955397371 :=
  prime_of_pocklington (a := 2) (all_1 p_255515944373312847190720520512484175977) (by decide +kernel)

/-- **The field modulus `P = 2²⁵⁶ − 2³² − 977` is prime.** -/
theorem P_prime : IsPrime Secp.P :=
  prime_of_pocklington (a := 2)
    (all_1 p_205115282021455665897114700593932402728804164701536103180137503955397371)
    (by decide +kernel)

/-- **The curve order `N` is prime.** -/
theorem N_prime : IsPrime Secp.Spec.N :=
  prime_of_pocklington (a := 2)
    (all_2 p_341948486974166000522343609283189 p_174723607534414371449)
    (by decide +kernel)

/-- **Fermat's little theorem for `P`**, proved unconditionally. -/
theorem fermat_P (a : Nat) (h : a % Secp.P ≠ 0) : a ^ (Secp.P - 1) % Secp.P = 1 :=
  fermat_of_prime P_prime a h

/-- **Fermat's little theorem for `N`**, proved unconditionally. -/
theorem fermat_N (a : Nat) (h : a % Secp.Spec.N ≠ 0) : a ^ (Secp.Spec.N - 1) % Secp.Spec.N = 1 :=
  fermat_of_prime N_prime a h

theorem power_inverse_P (a : Nat) (h : a % Secp.P ≠ 0) : a * a ^ (Secp.P - 2) % Secp.P = 1 := by
  rw [show a * a ^ (Secp.P - 2) = a ^ (Secp.P - 1) by
    rw [show Secp.P - 1 = Secp.P - 2 + 1 by decide, Nat.pow_succ']]
  exact fermat_P a h

theorem power_inverse_N (a : Nat) (h : a % Secp.Spec.N ≠ 0) : a * a ^ (Secp.Spec.N - 2) % Secp.Spec.N = 1 := by
  rw [show a * a ^ (Secp.Spec.N - 2) = a ^ (Secp.Spec.N - 1) by
    rw [show Secp.Spec.N - 1 = Secp.Spec.N - 2 + 1 by decide, Nat.pow_succ']]
  exact fermat_N a h

/-- −7 is not a cube modulo P: raised to the power `(P − 1)/3` it does not give `1`. -/
theorem minus_seven_not_cube : (Secp.P - 7) ^ ((Secp.P - 1) / 3) % Secp.P ≠ 1 := by
  rw [← powMod_eq]
  decide +kernel

/-- No number cubed is −7 modulo P. -/
theorem no_cube_root (a : Nat) : (a ^ 3 + 7) % Secp.P ≠ 0 := by
  intro h
  have cube : a ^ 3 % Secp.P = Secp.P - 7 := by
    have lt := Nat.mod_lt (a ^ 3) (show 0 < Secp.P by decide)
    rw [Nat.add_mod] at h
    generalize a ^ 3 % Secp.P = r at *
    simp only [Secp.P] at *
    omega
  have nonzero : a % Secp.P ≠ 0 := by
    intro zero
    rw [Nat.pow_mod, zero] at cube
    exact absurd cube (by decide)
  have fermat := fermat_P a nonzero
  rw [show Secp.P - 1 = 3 * ((Secp.P - 1) / 3) by decide, Nat.pow_mul, Nat.pow_mod, cube] at fermat
  exact minus_seven_not_cube fermat

end Secp.Primes

namespace Secp.Spec

theorem inv_exists {a : F} (ha : a ≠ 0) : ∃ w, a * w = 1 := by
  refine ⟨Fin.ofNat P (a.val ^ (P - 2)), ?_⟩
  apply Fin.ext
  have nonzero : a.val % P ≠ 0 := by
    rw [Nat.mod_eq_of_lt a.isLt]
    exact fun e => ha (Fin.ext e)
  rw [Fin.val_mul]
  show a.val * (a.val ^ (P - 2) % P) % P = 1
  rw [Nat.mul_mod_mod]
  exact Secp.Primes.power_inverse_P a.val nonzero

theorem mul_inv {a : F} (h : a ≠ 0) : a * inv a = 1 := by
  have he := inv_exists h
  simp only [inv, he, dite_true]
  exact Classical.choose_spec he

theorem inv_mul {a : F} (h : a ≠ 0) : inv a * a = 1 := by
  have := mul_inv h; grind

theorem mul_eq_zero {a b : F} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have := mul_inv ha
    calc b = (a * inv a) * b := by rw [this]; grind
      _ = inv a * (a * b) := by grind
      _ = 0 := by rw [h]; grind

theorem mul_ne_zero {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro e; rcases mul_eq_zero e with e | e
  · exact ha e
  · exact hb e

theorem two_ne_zero : (2 : F) ≠ 0 := by decide
theorem three_ne_zero : (3 : F) ≠ 0 := by decide

/-- No curve point on `y² = x³ + 7` over `F` has `y = 0` (no 2-torsion). -/
theorem onCurve_y_ne_zero {x y : F} (h : y * y = x * x * x + 7) : y ≠ 0 := by
  intro zero
  rw [zero] at h
  have val := congrArg Fin.val h
  apply Secp.Primes.no_cube_root x.val
  have seven : (7 : F).val = 7 := by decide
  have nothing : ((0 : F) * 0).val = 0 := by decide
  rw [nothing, Fin.val_add, Fin.val_mul, Fin.val_mul, seven, Nat.mod_mul_mod, Nat.mod_add_mod] at val
  rw [show x.val ^ 3 = x.val * x.val * x.val by rw [Nat.pow_succ, Nat.pow_two]]
  exact val.symm

end Secp.Spec
