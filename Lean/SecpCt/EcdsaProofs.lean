import SecpCt.SignProofs
import SecpCt.Ecdsa

/-! # ECDSA

`Ecdsa.signRaw_eq` and `Ecdsa.sign_eq`: whenever the reference (`Secp.Ecdsa.signWith`, `Secp/Signing.lean`,
over the specification's own `k·G`) gives a signature for a key, a digest and 32 bytes of randomness, the
constant-time code gives the same sixty-four bytes. The reference is the textbook steps on plain numbers and
is not something that runs; the constant-time code is what handles the key; this says it comes to the same
bytes on every input.

It follows the steps in order: the key as a number, the secret number the signature is made with, its
point's x reduced modulo N, the division, the sum, and the choice of the lower half. What is new beside the
BIP 340 proof (`SecpCt/SignProofs.lean`) is the division: `Sc.inv` is shown to be the power N − 2
(`Sc.inv_spec`), which is how the reference writes it too (`Secp.Ecdsa.inverse_eq`), and `Sc.isHigh` is
shown to say whether a number is above N/2 (`Sc.isHigh_spec`).

One thing is assumed, as a hypothesis and never as an axiom: that P is prime, as Fermat's little theorem for
P (`SecpCt/CurveProofs.lean`), since the point's x is found by a division modulo P.

What is not proved: that a signature the reference gives is one the verifier accepts. That needs the curve's
group law and N to be prime, neither of which is proved. So that step is checked each time instead of once:
`Ecdsa.signVerified` puts the signature to `Ecdsa.verify` before letting it out, and what that accepting
means is `Ecdsa.verify_sound` (`SecpCt/KeySpecs.lean`).

Nothing that runs imports this file; `SecpCt/Gate.lean` does. -/

namespace SecpCt
open Secp.Spec (F FieldP)
open Secp

/-! ## The scalars ECDSA adds: one, powers, the inverse, the upper half -/

theorem Sc.one_toNat : Sc.one.toNat = 1 := by
  simp only [Sc.one, Sc.toNat, value, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl]

/-- What one bit of the exponent does to the running power: square, and multiply if the bit is set. -/
def Sc.powerStep (a : Sc) (word : UInt64) (s : Sc) (i : Nat) : Sc :=
  if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then (s.mul s).mul a else s.mul s

theorem Sc.power_loop (l : List Nat) (a : Sc) (word : UInt64) (r : Sc) :
    (forIn l r (fun i s => if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then pure (ForInStep.yield ((s.mul s).mul a))
      else pure (ForInStep.yield (s.mul s))) : Id Sc).run = l.foldl (Sc.powerStep a word) r := by
  have body : (fun (i : Nat) (s : Sc) => (if word >>> UInt64.ofNat (63 - i) &&& 1 = 1 then pure (ForInStep.yield ((s.mul s).mul a))
      else pure (ForInStep.yield (s.mul s)) : Id (ForInStep Sc))) = fun i s => pure (ForInStep.yield (Sc.powerStep a word s i)) := by
    funext i s
    simp only [Sc.powerStep]
    split <;> rfl
  rw [body, List.forIn_pure_yield_eq_foldl]
  rfl

theorem Sc.power_fold (a : Sc) (e0 e1 e2 e3 : UInt64) :
    Sc.power a e0 e1 e2 e3 = (List.range' 0 64).foldl (Sc.powerStep a e0) ((List.range' 0 64).foldl (Sc.powerStep a e1)
      ((List.range' 0 64).foldl (Sc.powerStep a e2) ((List.range' 0 64).foldl (Sc.powerStep a e3) Sc.one))) := by
  simp [Sc.power, -List.foldl_cons, Sc.power_loop]

/-- Along the bits of a word, the running power keeps being `a` to the exponent reached so far. -/
theorem Sc.power_bits (l : List Nat) (a : Sc) (word : UInt64) (r : Sc) (e : Nat) (h : r.toNat = a.toNat ^ e % N) :
    (l.foldl (Sc.powerStep a word) r).toNat = a.toNat ^ (l.foldl (exponentStep word) e) % N := by
  induction l generalizing r e with
  | nil => exact h
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    have squared : (r.mul r).toNat = a.toNat ^ (2 * e) % N := by
      rw [Sc.mul_spec, h, ← Nat.mul_mod, ← Nat.pow_add, Nat.two_mul]
    simp only [Sc.powerStep, exponentStep]
    split
    · rw [Sc.mul_spec, squared, Nat.mod_mul_mod, Nat.pow_succ]
    · exact squared

/-- `power` is `a` to the exponent its four words spell, modulo N. -/
theorem Sc.power_spec (a : Sc) (e0 e1 e2 e3 : UInt64) :
    (Sc.power a e0 e1 e2 e3).toNat = a.toNat ^ ((List.range' 0 64).foldl (exponentStep e0)
      ((List.range' 0 64).foldl (exponentStep e1) ((List.range' 0 64).foldl (exponentStep e2)
        ((List.range' 0 64).foldl (exponentStep e3) 0)))) % N := by
  rw [Sc.power_fold]
  exact Sc.power_bits _ a e0 _ _ (Sc.power_bits _ a e1 _ _ (Sc.power_bits _ a e2 _ _
    (Sc.power_bits _ a e3 _ 0 (by rw [Nat.pow_zero, Sc.one_toNat]; rfl))))

/-- The four words `inv` raises to spell N − 2. -/
theorem Sc.inv_exponent :
    (List.range' 0 64).foldl (exponentStep 0xBFD25E8CD036413F) ((List.range' 0 64).foldl
      (exponentStep 0xBAAEDCE6AF48A03B) ((List.range' 0 64).foldl (exponentStep 0xFFFFFFFFFFFFFFFE)
        ((List.range' 0 64).foldl (exponentStep 0xFFFFFFFFFFFFFFFF) 0))) = N - 2 := by
  decide +kernel

/-- `inv` is `a` to the power N − 2, modulo N. -/
theorem Sc.inv_spec (a : Sc) : (Sc.inv a).toNat = a.toNat ^ (N - 2) % N := by
  rw [Sc.inv, Sc.power_spec, Sc.inv_exponent]

/-- The four words `isHigh` compares with are (N − 1)/2, which is N/2 rounded down. -/
theorem half_words : value Sc.half0 Sc.half1 Sc.half2 Sc.half3 = N / 2 := by decide

/-- The arithmetic of `isHigh`: taking `a` from `h` borrows exactly when `a` is the larger. `d` is what is
left, `b` the borrow. -/
theorem borrow_iff (d a h b : Nat) (e : d + a = h + b * 2 ^ 256) (hb : b ≤ 1) (hd : d < 2 ^ 256) :
    b = if a > h then 1 else 0 := by
  simp only [Nat.reducePow] at *
  by_cases big : a > h <;> simp only [big, ↓reduceIte] <;> omega

/-- `isHigh` is 1 for a scalar above N/2 and 0 for every other. -/
theorem Sc.isHigh_spec (a : Sc) : Sc.isHigh a = if a.toNat > N / 2 then 1 else 0 := by
  obtain ⟨e, hb⟩ := sbb4_spec Sc.half0 Sc.half1 Sc.half2 Sc.half3 a.a0 a.a1 a.a2 a.a3
  have hd := value_lt (sbb Sc.half0 a.a0 0).1 (sbb Sc.half1 a.a1 (sbb Sc.half0 a.a0 0).2).1
    (sbb Sc.half2 a.a2 (sbb Sc.half1 a.a1 (sbb Sc.half0 a.a0 0).2).2).1
    (sbb Sc.half3 a.a3 (sbb Sc.half2 a.a2 (sbb Sc.half1 a.a1 (sbb Sc.half0 a.a0 0).2).2).2).1
  rw [half_words] at e
  have bit := borrow_iff _ _ _ _ e hb hd
  simp only [Sc.isHigh]
  apply UInt64.toNat_inj.mp
  rw [bit]
  by_cases big : a.toNat > N / 2
  · have same : value a.a0 a.a1 a.a2 a.a3 > N / 2 := big
    simp only [big, same, ↓reduceIte]
    rfl
  · have same : ¬ value a.a0 a.a1 a.a2 a.a3 > N / 2 := big
    simp only [big, same, ↓reduceIte]
    rfl

/-! ## The reference's division is the same power -/

/-- The reference's `1/k` is `k` to the power N − 2, modulo N, with N as this library writes it. -/
theorem Ecdsa.reference_inverse (k : Nat) : Secp.Ecdsa.inverse k = k ^ (N - 2) % N := by
  rw [Secp.Ecdsa.inverse_eq, N_eq]

/-! ## The signature -/

/-- The arithmetic of the lower half: for `s` from 1 to N − 1 above N/2, `N − s` is below N. -/
theorem lower_half (s : Nat) (below : s < N) : (N - s) % N = if s = 0 then 0 else N - s := by
  by_cases zero : s = 0
  · simp only [zero, ↓reduceIte, Nat.sub_zero, Nat.mod_self]
  · simp only [zero, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)

/-- **The signature is the reference's.** Whenever the reference gives an ECDSA signature for the number
thirty-two bytes of secret spell, `signRaw` gives the same `r` and `s`, as bytes, and says they are a
signature. -/
theorem Ecdsa.signRaw_eq [Fermat] (secret digest aux : ByteArray) (size : secret.size = 32) {r s : Nat}
    (h : Secp.Ecdsa.signWith Spec.mulG digest (Secp.fromBE secret) aux = some (r, s)) :
    SecpCt.Ecdsa.signRaw secret digest aux = (Secp.toBE32 r ++ Secp.toBE32 s, 1) := by
  unfold Secp.Ecdsa.signWith at h
  rw [← N_eq] at h
  by_cases hd : Secp.fromBE secret = 0 ∨ Secp.fromBE secret ≥ N
  · simp [hd] at h
  by_cases hs : aux.size ≠ 32 ∨ digest.size ≠ 32
  · simp [hd, hs] at h
  simp only [hd, hs, ↓reduceIte] at h
  have positive : 0 < Secp.fromBE secret := by omega
  have below : Secp.fromBE secret < N := by omega
  have digestSize : digest.size = 32 := by omega
  have secretNumber : (Sc.ofBytes secret).toNat = Secp.fromBE secret := by
    rw [Sc.ofBytes_spec secret size, Nat.mod_eq_of_lt below]
  have key : Sc.isKey secret = 1 := by
    rw [Sc.isKey_spec secret size]
    simp only [positive, below, and_self, ↓reduceIte]
  generalize hk : Secp.Ecdsa.nonce (Secp.fromBE secret) digest aux = k at h
  by_cases hz : k = 0
  · simp [hz] at h
  simp only [hz, ↓reduceIte] at h
  cases hg : Spec.mulG k with
  | none => rw [hg] at h; cases h
  | some q =>
    rw [hg] at h
    cases q with
    | mk rx ry =>
      simp only at h
      generalize hr : rx % N = r0 at h
      by_cases hr0 : r0 = 0
      · simp [hr0] at h
      simp only [hr0, ↓reduceIte] at h
      generalize hs0 : Secp.Ecdsa.inverse k * ((Secp.fromBE digest % N + r0 * Secp.fromBE secret % N) % N) % N
        = s0 at h
      by_cases hs00 : s0 = 0
      · simp [hs00] at h
      simp only [hs00, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [SecpCt.Ecdsa.signRaw]
      -- the key's bytes are winnow's, and so the number the signature is made with
      have dBytes : (Sc.ofBytes secret).bytes = toBE32 (Secp.fromBE secret) := by
        rw [Sc.bytes_spec, secretNumber]
      simp only [dBytes]
      rw [xor32_eq _ _ (toBE32_size _) (tagged_size _ _)]
      have nonce := Sc.ofBytes_spec _ (tagged_size "winnow/ecdsa/nonce"
        (xorBytes (toBE32 (Secp.fromBE secret)) (Sha256.tagged "winnow/ecdsa/aux" aux) ++ digest))
      rw [N_eq] at nonce
      change _ = Secp.Ecdsa.nonce (Secp.fromBE secret) digest aux at nonce
      rw [hk] at nonce
      generalize Sc.ofBytes (Sha256.tagged "winnow/ecdsa/nonce" _) = ks at *
      -- its point's x, modulo N
      obtain ⟨hrx, _⟩ := affine_of_smul ks rx ry (by rw [nonce]; exact hg)
      have rNumber : (Sc.reduceOnce (Point.mulGenerator ks).affine.1.a0 (Point.mulGenerator ks).affine.1.a1
          (Point.mulGenerator ks).affine.1.a2 (Point.mulGenerator ks).affine.1.a3 0).toNat = r0 := by
        rw [reduceOnce_mod]
        show (Point.mulGenerator ks).affine.1.toNat % N = r0
        rw [hrx, hr]
      generalize Sc.reduceOnce (Point.mulGenerator ks).affine.1.a0 (Point.mulGenerator ks).affine.1.a1
          (Point.mulGenerator ks).affine.1.a2 (Point.mulGenerator ks).affine.1.a3 0 = rs at *
      -- the digest, the sum and the division
      have zNumber := Sc.ofBytes_spec digest digestSize
      have zBelow : (Sc.ofBytes digest).toNat < N := by
        rw [zNumber]
        exact Nat.mod_lt _ (by decide)
      generalize Sc.ofBytes digest = zs at *
      generalize Sc.ofBytes secret = ds at *
      have sNumber : (Sc.mul (Sc.inv ks) (Sc.add zs (Sc.mul rs ds))).toNat = s0 := by
        rw [Sc.mul_spec, Sc.inv_spec, Sc.add_spec zs _ zBelow (Sc.mul_lt _ _), Sc.mul_spec, zNumber, rNumber,
          secretNumber, nonce, ← Ecdsa.reference_inverse, hs0]
      have sBelow : (Sc.mul (Sc.inv ks) (Sc.add zs (Sc.mul rs ds))).toNat < N := Sc.mul_lt _ _
      generalize Sc.mul (Sc.inv ks) (Sc.add zs (Sc.mul rs ds)) = ss at *
      -- the lower half
      have chosen : (Sc.negIf (Sc.isHigh ss) ss).toNat = Secp.Ecdsa.lowS s0 := by
        rw [Sc.isHigh_spec, sNumber, Secp.Ecdsa.lowS, ← N_eq]
        by_cases high : s0 > N / 2
        · simp only [high, ↓reduceIte]
          rw [Sc.negIf_one, Sc.neg_spec ss sBelow, sNumber, lower_half s0 (sNumber ▸ sBelow)]
          simp only [hs00, ↓reduceIte]
        · simp only [high, ↓reduceIte]
          rw [Sc.negIf_zero, sNumber]
      have chosenNonzero : Secp.Ecdsa.lowS s0 ≠ 0 := by
        have := sNumber ▸ sBelow
        rw [Secp.Ecdsa.lowS, ← N_eq]
        split <;> omega
      rw [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · rw [Sc.bytes_spec, Sc.bytes_spec, rNumber, chosen]
      · rw [key, Sc.isZero_spec, Sc.isZero_spec, Sc.isZero_spec, nonce, rNumber, chosen]
        simp only [hz, hr0, chosenNonzero, ↓reduceIte]
        rfl

/-- **`Ecdsa.sign` returns the reference's signature.** Whenever the reference gives an ECDSA signature for
the number thirty-two bytes of secret spell, `Ecdsa.sign` returns it: `r` then `s`, sixty-four bytes. -/
theorem Ecdsa.sign_eq [Fermat] (secret digest aux : ByteArray) (size : secret.size = 32) {signature : ByteArray}
    (h : (Secp.Ecdsa.signWith Spec.mulG digest (Secp.fromBE secret) aux).map Secp.Ecdsa.encode = some signature) :
    SecpCt.Ecdsa.sign secret digest aux = some signature := by
  cases hr : Secp.Ecdsa.signWith Spec.mulG digest (Secp.fromBE secret) aux with
  | none => rw [hr] at h; cases h
  | some pair =>
    obtain ⟨r, s⟩ := pair
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have raw := Ecdsa.signRaw_eq secret digest aux size hr
    have sizes : aux.size = 32 ∧ digest.size = 32 := by
      unfold Secp.Ecdsa.signWith at hr
      by_cases hd : Secp.fromBE secret = 0 ∨ Secp.fromBE secret ≥ Spec.N
      · simp [hd] at hr
      by_cases hs : aux.size ≠ 32 ∨ digest.size ≠ 32
      · simp [hd, hs] at hr
      omega
    simp only [SecpCt.Ecdsa.sign, size, sizes.1, sizes.2, raw]
    rfl

end SecpCt
