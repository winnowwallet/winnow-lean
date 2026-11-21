import SecpCt.KeySpecs
import Secp.Proofs.Der

/-! # Generator order `N`, key-serialization round-trips, and signing completeness

Closes the remaining completeness properties on `SecpCt`:

1. **Generator order `N` (`smul_N_G`, `smul_G_ne_inf`, `nsmul_mod_N`):**
   `N · G = .inf`, scalar multiples of `G` depend only on the exponent modulo `N`, and no scalar `1 ≤ d < N`
   sends `G` to `.inf` (via `Secp.Primes.N_prime` + Bézout).
2. **Serialization & `lift_x` round-trips (`Fe.sqrt?_complete`, `parseXOnly_xBytes`, `parseCompressed_compressed`):**
   Every valid `Affine` curve point round-trips losslessly through `compressed` bytes, and its `xBytes` lifts
   to the unique even-`y` partner.
3. **Unconditional signing completeness (`verify_sign`, `signVerified_eq_sign`, `Ecdsa.verify_sign`,
   `Ecdsa.signVerified_eq_sign`):**
   Every signature produced by `SecpCt.sign` (BIP 340) or `SecpCt.Ecdsa.sign` (low-S ECDSA) is accepted by
   `verify` / `Ecdsa.verify` under the signer's own public key, so the runtime fault-check wrappers
   `signVerified` and `Ecdsa.signVerified` are mathematically identical to `sign` and `Ecdsa.sign`. -/

namespace SecpCt
open Secp.Spec (F OnCurve)
open Secp

/-! ## Word and element injectivity, negation, and `Affine` extensionality -/

theorem value_inj {a0 a1 a2 a3 b0 b1 b2 b3 : UInt64}
    (h : value a0 a1 a2 a3 = value b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have ha0 := a0.toNat_lt; have ha1 := a1.toNat_lt; have ha2 := a2.toNat_lt; have ha3 := a3.toNat_lt
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  simp only [value, Nat.reducePow] at h
  exact ⟨UInt64.toNat_inj.mp (by omega), UInt64.toNat_inj.mp (by omega),
         UInt64.toNat_inj.mp (by omega), UInt64.toNat_inj.mp (by omega)⟩

theorem Fe.toNat_inj {a b : Fe} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b
  obtain ⟨rfl, rfl, rfl, rfl⟩ := value_inj h
  rfl

theorem Sc.toNat_inj {a b : Sc} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b
  obtain ⟨rfl, rfl, rfl, rfl⟩ := value_inj h
  rfl

theorem Fe.toF_inj {a b : Fe} (ha : a.Valid) (hb : b.Valid) (h : a.toF = b.toF) : a = b := by
  apply Fe.toNat_inj
  have hv := congrArg Fin.val h
  rw [Fe.toF_val, Fe.toF_val, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hv

@[simp] theorem Fe.same_refl (a : Fe) : Fe.same a a = true := by
  cases a; simp [Fe.same]

@[simp] theorem Sc.same_refl (a : Sc) : Sc.same a a = true := by
  cases a; simp [Sc.same]

theorem Fe.same_iff {a b : Fe} : Fe.same a b = true ↔ a = b :=
  ⟨Fe.same_eq, fun h => h ▸ Fe.same_refl a⟩

theorem Sc.same_iff {a b : Sc} : Sc.same a b = true ↔ a = b :=
  ⟨Sc.same_eq, fun h => h ▸ Sc.same_refl a⟩

theorem Fe.neg_neg {y : Fe} (hy : y.Valid) : Fe.neg (Fe.neg y) = y := by
  apply Fe.toF_inj (valid_neg _ (valid_neg _ hy)) hy
  rw [toF_neg _ (valid_neg _ hy), toF_neg _ hy]
  exact (show ∀ {R : Type} [Lean.Grind.CommRing R] (x : R), - -x = x by intro _ _ _; grind) y.toF

theorem Affine.neg_neg {p : Affine} (hp : p.Good) : p.neg.neg = p := by
  unfold Affine.neg
  dsimp only
  rw [Fe.neg_neg hp.2.1]

theorem Affine.ext_good {p q : Affine} (hp : p.Good) (hq : q.Good) (hx : p.x = q.x) (hy : p.y = q.y) :
    p = q := by
  have hneg : p.neg = q.neg := by
    unfold Affine.neg
    rw [hx, hy]
  rw [← Affine.neg_neg hp, ← Affine.neg_neg hq, hneg]

theorem Affine.ext_spec {p q : Affine} (hp : p.Good) (hq : q.Good) (hs : p.spec = q.spec) : p = q := by
  simp only [Affine.spec, Spec.Point.pt.injEq] at hs
  exact Affine.ext_good hp hq (Fe.toF_inj hp.1 hq.1 hs.1) (Fe.toF_inj hp.2.1 hq.2.1 hs.2)

/-! ## Big-endian 32-byte round-trips and slicing -/

private theorem fromBE_toBE32_step (n : Nat) :
    ∀ k : Nat,
      ((List.range k).reverse.map fun j => UInt8.ofNat (n / 2 ^ (8 * j))).foldl
        (fun acc (x : UInt8) => acc * 256 + x.toNat) (n / 2 ^ (8 * k)) = n
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, List.foldl_cons]
    have hpow : n / 2 ^ (8 * (k + 1)) = n / 2 ^ (8 * k) / 256 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.div_div_eq_div_mul]
    have hstep : n / 2 ^ (8 * (k + 1)) * 256 + (UInt8.ofNat (n / 2 ^ (8 * k))).toNat = n / 2 ^ (8 * k) := by
      rw [hpow, UInt8.toNat_ofNat']
      show n / 2 ^ (8 * k) / 256 * 256 + n / 2 ^ (8 * k) % 256 = n / 2 ^ (8 * k)
      have := Nat.div_add_mod (n / 2 ^ (8 * k)) 256
      omega
    rw [hstep]
    exact fromBE_toBE32_step n k

theorem fromBE_toBE32_mod (n : Nat) : Secp.fromBE (Secp.toBE32 n) = n % 2 ^ 256 := by
  have hrev : (List.range 32).map (fun i => 31 - i) = (List.range 32).reverse := by decide +kernel
  unfold Secp.fromBE Secp.toBE32
  rw [foldl_bytes, Array.toList_map]
  have htl : (List.range 32).toArray.toList = List.range 32 := rfl
  rw [htl]
  have hmap : ((List.range 32).map fun i => UInt8.ofNat (n / 2 ^ (8 * (31 - i)))) =
      ((List.range 32).reverse.map fun j => UInt8.ofNat ((n % 2 ^ 256) / 2 ^ (8 * j))) := by
    rw [← hrev, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat']
    show n / 2 ^ (8 * (31 - i)) % 256 = n % 2 ^ 256 / 2 ^ (8 * (31 - i)) % 256
    have hsplit : 2 ^ 256 = 2 ^ (8 * (31 - i)) * (256 * 2 ^ (8 * i)) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
      congr 1; omega
    have hmod_div : ∀ a b c : Nat, 0 < b → 0 < c → a % (b * c) / b = (a / b) % c := by
      intro a b c hb hc
      have hdiv := Nat.div_add_mod a (b * c)
      have hlt : a % (b * c) < b * c := Nat.mod_lt a (Nat.mul_pos hb hc)
      have h1 : a = b * (c * (a / (b * c))) + a % (b * c) := by
        have : b * c * (a / (b * c)) = b * (c * (a / (b * c))) := by grind
        omega
      conv => rhs; rw [h1]
      rw [Nat.mul_add_div hb, Nat.add_comm, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hlt)]
    rw [hsplit, hmod_div n (2 ^ (8 * (31 - i))) (256 * 2 ^ (8 * i)) (Nat.two_pow_pos _)
        (Nat.mul_pos (by decide) (Nat.two_pow_pos _))]
    have hmod2 : ∀ x k : Nat, x % (256 * k) % 256 = x % 256 := by
      intro x k
      have hd := Nat.div_add_mod x (256 * k)
      conv => rhs; rw [← hd, show 256 * k * (x / (256 * k)) = 256 * (k * (x / (256 * k))) by grind]
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [hmod2]
  rw [hmap]
  have hzero : (n % 2 ^ 256) / 2 ^ (8 * 32) = 0 :=
    Nat.div_eq_of_lt (Nat.mod_lt n (Nat.two_pow_pos 256))
  rw [← hzero]
  exact fromBE_toBE32_step (n % 2 ^ 256) 32

theorem fromBE_toBE32 {n : Nat} (hn : n < 2 ^ 256) : Secp.fromBE (Secp.toBE32 n) = n := by
  rw [fromBE_toBE32_mod, Nat.mod_eq_of_lt hn]

theorem Fe.bytes_size (a : Fe) : a.bytes.size = 32 := by
  rw [Fe.bytes_spec, toBE32_size]

theorem Sc.bytes_size (a : Sc) : a.bytes.size = 32 := by
  rw [Sc.bytes_spec, toBE32_size]

theorem Fe.fromBE_bytes (a : Fe) : Secp.fromBE a.bytes = a.toNat := by
  rw [Fe.bytes_spec]
  exact fromBE_toBE32 (value_lt a.a0 a.a1 a.a2 a.a3)

theorem Sc.fromBE_bytes (a : Sc) : Secp.fromBE a.bytes = a.toNat := by
  rw [Sc.bytes_spec]
  exact fromBE_toBE32 (value_lt a.a0 a.a1 a.a2 a.a3)

theorem Fe.ofBytes_bytes {a : Fe} (ha : a.Valid) : Fe.ofBytes a.bytes = a := by
  apply Fe.toNat_inj
  rw [Fe.ofBytes_spec _ (Fe.bytes_size a), Fe.fromBE_bytes, Nat.mod_eq_of_lt ha]

theorem Sc.ofBytes_bytes {a : Sc} (ha : a.toNat < N) : Sc.ofBytes a.bytes = a := by
  apply Sc.toNat_inj
  rw [Sc.ofBytes_spec _ (Sc.bytes_size a), Sc.fromBE_bytes, Nat.mod_eq_of_lt ha]

theorem Fe.ofBytes?_bytes {a : Fe} (ha : a.Valid) : Fe.ofBytes? a.bytes = some a := by
  have hsz := Fe.bytes_size a
  unfold Fe.ofBytes?
  simp only [hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Fe.ofBytes_bytes ha]
  have hw : (⟨wordAt a.bytes 24, wordAt a.bytes 16, wordAt a.bytes 8, wordAt a.bytes 0⟩ : Fe) = a := by
    apply Fe.toNat_inj
    have hf := Fe.fromBE_bytes a
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
      b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, heq⟩ := bytes32 a.bytes hsz
    rw [heq, fromBE_words] at hf
    simp only [Fe.toNat] at hf
    simp only [heq, Fe.toNat]
    exact hf
  simp [hw]

theorem scalar?_bytes {s : Sc} (hs : s.toNat < N) : scalar? s.bytes = some s := by
  have hsz := Sc.bytes_size s
  unfold scalar?
  rw [Sc.isBelowN_spec _ hsz, Sc.fromBE_bytes]
  simp only [hsz, hs, ↓reduceIte, beq_self_eq_true, Bool.and_self, Sc.ofBytes_bytes hs]

private theorem extract_toList_eq (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = (b.data.toList.drop s).take (e - s) := by
  have hlen (x : ByteArray) : x.data.toList.length = x.size := Array.length_toList
  apply List.ext_getElem
  · rw [hlen, ByteArray.size_extract, List.length_take, List.length_drop, hlen]
    omega
  · intro i h1 h2
    rw [hlen, ByteArray.size_extract] at h1
    rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_extract,
        List.getElem_take, List.getElem_drop, Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

private theorem append_toList_eq (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  have hlen (x : ByteArray) : x.data.toList.length = x.size := Array.length_toList
  apply List.ext_getElem
  · rw [hlen, ByteArray.size_append, List.length_append, hlen, hlen]
  · intro i h1 h2
    rw [hlen, ByteArray.size_append] at h1
    by_cases hi : i < a.size
    · have hi' : i < a.data.toList.length := by rw [hlen]; exact hi
      rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_append_left hi,
          List.getElem_append_left hi', Array.getElem_toList, ByteArray.getElem_eq_getElem_data]
    · have hge : a.size ≤ i := by omega
      have hge' : a.data.toList.length ≤ i := by rw [hlen]; exact hge
      rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_append_right hge,
          List.getElem_append_right hge']
      simp only [hlen, Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

theorem extract_append_left (a b : ByteArray) : (a ++ b).extract 0 a.size = a := by
  apply bytes_ext
  rw [extract_toList_eq, append_toList_eq]
  have hlen : a.data.toList.length = a.size := Array.length_toList
  rw [List.drop_zero, Nat.sub_zero, List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.take_of_length_le (Nat.le_of_eq hlen)]

theorem extract_append_right (a b : ByteArray) : (a ++ b).extract a.size (a.size + b.size) = b := by
  apply bytes_ext
  rw [extract_toList_eq, append_toList_eq]
  have hlen_a : a.data.toList.length = a.size := Array.length_toList
  have hlen_b : b.data.toList.length = b.size := Array.length_toList
  rw [List.drop_append, List.drop_of_length_le (Nat.le_of_eq hlen_a), List.nil_append,
      hlen_a, Nat.sub_self, List.drop_zero, show a.size + b.size - a.size = b.size by omega,
      List.take_of_length_le (Nat.le_of_eq hlen_b)]

/-! ## Completeness of `Fe.sqrt?`, `liftX?`, `parseXOnly`, and `parseCompressed` -/

theorem sqrt_exponent :
    (List.range' 0 64).foldl (exponentStep 0xFFFFFFFFBFFFFF0C) ((List.range' 0 64).foldl
      (exponentStep 0xFFFFFFFFFFFFFFFF) ((List.range' 0 64).foldl (exponentStep 0xFFFFFFFFFFFFFFFF)
        ((List.range' 0 64).foldl (exponentStep 0x3FFFFFFFFFFFFFFF) 0))) = (P + 1) / 4 := by
  decide +kernel

theorem Fe.sqrt?_complete {a y : Fe} (ha : a.Valid) (hy : y.toF * y.toF = a.toF) :
    ∃ r, Fe.sqrt? a = some r := by
  unfold Fe.sqrt?
  let root := Fe.power a 0xFFFFFFFFBFFFFF0C 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0x3FFFFFFFFFFFFFFF
  have hroot : root.toNat = a.toNat ^ ((P + 1) / 4) % P := by
    dsimp [root]; rw [power_spec, sqrt_exponent]
  have hsq_eq : Fe.sqr root = a := by
    apply Fe.toNat_inj
    rw [Fe.sqr, mul_spec, hroot, ← Nat.mul_mod, ← Nat.pow_add]
    have hexp2 : (P + 1) / 4 + (P + 1) / 4 = (P + 1) / 2 := by decide
    rw [hexp2]
    have hy_nat : y.toNat * y.toNat % P = a.toNat := by
      have hv := congrArg Fin.val hy
      rw [Fin.val_mul, Fe.toF_val, Fe.toF_val, ← P_eq, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_eq_of_lt ha] at hv
      exact hv
    by_cases ha0 : a.toNat = 0
    · rw [ha0, Nat.zero_pow (by decide), Nat.zero_mod]
    · have hy_nz : y.toNat % Secp.P ≠ 0 := by
        intro hz
        rw [P_eq] at hy_nat
        rw [Nat.mul_mod, hz, Nat.zero_mul, Nat.zero_mod] at hy_nat
        exact ha0 hy_nat.symm
      have hfermat := Secp.Primes.fermat_P y.toNat hy_nz
      rw [← P_eq] at hfermat
      have hpow_y : a.toNat ^ ((P + 1) / 2) % P = (y.toNat * y.toNat) ^ ((P + 1) / 2) % P := by
        rw [← hy_nat, ← Nat.pow_mod]
      rw [hpow_y, ← Nat.pow_two, ← Nat.pow_mul]
      have hexp_mul : 2 * ((P + 1) / 2) = 2 + (P - 1) := by decide
      rw [hexp_mul, Nat.pow_add, Nat.pow_two, Nat.mul_mod, hy_nat, hfermat, Nat.mul_one, Nat.mod_eq_of_lt ha]
  refine ⟨root, ?_⟩
  dsimp only [root] at hsq_eq ⊢
  simp [hsq_eq]

theorem even_y_unique {x y1 y2 : Fe} (hy1 : y1.Valid) (hy2 : y2.Valid)
    (hc1 : y1.toF * y1.toF = x.toF * x.toF * x.toF + 7)
    (hc2 : y2.toF * y2.toF = x.toF * x.toF * x.toF + 7)
    (he1 : y1.toNat % 2 = 0) (he2 : y2.toNat % 2 = 0) : y1 = y2 := by
  rcases Spec.eq_or_neg_of_eq_x hc1 hc2 with hsame | hopp
  · exact Fe.toF_inj hy1 hy2 hsame
  · exfalso
    have hnz : y1.toF ≠ 0 := Spec.onCurve_y_ne_zero hc1
    have hy1_pos : 0 < y1.toNat := by
      apply Nat.pos_of_ne_zero
      intro hz; apply hnz; apply Fin.ext; rw [Fe.toF_val, hz, Nat.zero_mod]; rfl
    have hneg : y2.toF = (Fe.neg y1).toF := by rw [toF_neg _ hy1, hopp]
    have hyeq : y2 = Fe.neg y1 := Fe.toF_inj hy2 (valid_neg _ hy1) hneg
    have hy1_lt : y1.toNat < P := hy1
    have hval : y2.toNat = P - y1.toNat := by
      rw [hyeq, neg_spec _ hy1, Nat.mod_eq_of_lt (by omega)]
    have hp_odd := P_odd
    omega

theorem Affine.evenPartner_good {p : Affine} (hp : p.Good) :
    let q := if p.isOdd then p.neg else p
    q.Good ∧ q.x = p.x ∧ q.y.toNat % 2 = 0 ∧ q.isOdd = false := by
  dsimp only
  have parity := Fe.isOdd_spec p.y
  by_cases hodd : p.isOdd = true
  · have hite : (if p.isOdd then p.neg else p) = p.neg := by simp [hodd]
    rw [hite]
    have hp_odd : p.y.toNat % 2 = 1 := by
      simp only [Affine.isOdd, beq_iff_eq] at hodd
      rw [← parity, hodd]; rfl
    have hev : (Fe.neg p.y).toNat % 2 = 0 := neg_even p.y hp.2.1 hp_odd
    have hisOdd : p.neg.isOdd = false := by
      simp only [Affine.isOdd, Affine.neg, beq_eq_false_iff_ne]
      intro hc
      have h1 : (Fe.neg p.y).toNat % 2 = 1 := by rw [← Fe.isOdd_spec, hc]; rfl
      omega
    exact ⟨Affine.neg_good hp, rfl, hev, hisOdd⟩
  · simp only [Bool.not_eq_true] at hodd
    have hite : (if p.isOdd then p.neg else p) = p := by simp [hodd]
    rw [hite]
    have hp_not1 : p.y.isOdd ≠ 1 := by
      simp only [Affine.isOdd, beq_eq_false_iff_ne] at hodd; exact hodd
    have hev : p.y.toNat % 2 = 0 := by
      have hlt : p.y.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
      have hne1 : p.y.toNat % 2 ≠ 1 := fun e => hp_not1 (UInt64.toNat_inj.mp (by rw [parity, e]; rfl))
      omega
    exact ⟨hp, rfl, hev, hodd⟩

theorem liftX?_complete {p : Affine} (hp : p.Good) :
    liftX? p.x = some (if p.isOdd then p.neg else p) := by
  have hc : p.y.toF * p.y.toF = (Fe.add (Fe.mul (Fe.sqr p.x) p.x) seven).toF := by
    rw [cubic_toF]; exact hp.2.2
  obtain ⟨r, hr⟩ := Fe.sqrt?_complete (valid_add _ _ (valid_mul _ _) seven_valid) hc
  have hl : ∃ q, liftX? p.x = some q := by
    unfold liftX?; rw [hr]; exact ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hl
  rw [hq]
  congr 1
  obtain ⟨qx, qcurve, qy_val, qeven⟩ := liftX?_spec hq
  have qgood : q.Good := ⟨qx ▸ hp.1, qy_val, by show q.y.toF * q.y.toF = _; rw [qx]; exact qcurve⟩
  obtain ⟨pgood, px, peven, _⟩ := Affine.evenPartner_good hp
  have pcurve : (if p.isOdd then p.neg else p).y.toF * (if p.isOdd then p.neg else p).y.toF =
      p.x.toF * p.x.toF * p.x.toF + 7 := by
    have hc2 : (if p.isOdd then p.neg else p).y.toF * (if p.isOdd then p.neg else p).y.toF =
        (if p.isOdd then p.neg else p).x.toF * (if p.isOdd then p.neg else p).x.toF *
          (if p.isOdd then p.neg else p).x.toF + 7 := pgood.2.2
    rw [px] at hc2
    exact hc2
  exact Affine.ext_good qgood pgood (qx.trans px.symm)
    (even_y_unique (x := p.x) qy_val pgood.2.1 qcurve pcurve qeven peven)

private theorem bind_some_eq {α β : Type} (x : α) (f : α → Option β) :
    (some x).bind f = f x := rfl

private theorem option_bind_some_eq {α β : Type} (x : α) (f : α → Option β) :
    Option.bind (some x) f = f x := rfl

theorem parseXOnly_xBytes {p : Affine} (hp : p.Good) :
    parseXOnly p.xBytes = some (if p.isOdd then p.neg else p) := by
  unfold parseXOnly Affine.xBytes
  rw [Fe.ofBytes?_bytes hp.1, bind_some_eq]
  exact liftX?_complete hp

theorem parseXOnly_xBytes_even {p : Affine} (hp : p.Good) (heven : p.isOdd = false) :
    parseXOnly p.xBytes = some p := by
  rw [parseXOnly_xBytes hp, heven]
  rfl

theorem Affine.compressed_size (p : Affine) : p.compressed.size = 33 := by
  simp [Affine.compressed, ByteArray.size_append, Fe.bytes_size, show (ByteArray.mk #[_]).size = 1 from rfl]

theorem parseCompressed_compressed {p : Affine} (hp : p.Good) :
    parseCompressed p.compressed = some p := by
  have hsz := Affine.compressed_size p
  unfold parseCompressed
  simp only [hsz, ↓reduceDIte]
  have htag : p.compressed[0]'(by omega) = (2 ||| p.y.isOdd).toUInt8 := by
    simp [Affine.compressed, ByteArray.getElem_eq_getElem_data]
  have hex : p.compressed.extract 1 33 = p.xBytes := by
    have h1 : (ByteArray.mk #[(2 ||| p.y.isOdd).toUInt8]).size = 1 := rfl
    have h32 : p.x.bytes.size = 32 := Fe.bytes_size p.x
    have hslice := extract_append_right (ByteArray.mk #[(2 ||| p.y.isOdd).toUInt8]) p.x.bytes
    rw [h1, h32] at hslice
    exact hslice
  rw [htag, hex]
  have hbit : p.y.isOdd = 0 ∨ p.y.isOdd = 1 := by
    have := Fe.isOdd_spec p.y
    have hlt : p.y.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    rcases (show p.y.toNat % 2 = 0 ∨ p.y.toNat % 2 = 1 by omega) with h0 | h1
    · exact Or.inl (UInt64.toNat_inj.mp (by rw [this, h0]; rfl))
    · exact Or.inr (UInt64.toNat_inj.mp (by rw [this, h1]; rfl))
  rcases hbit with h0 | h1
  · have hisOdd : p.isOdd = false := by simp [Affine.isOdd, h0]
    have ht2 : ((2 ||| p.y.isOdd).toUInt8 : UInt8) = 2 := by rw [h0]; rfl
    rw [ht2, parseXOnly_xBytes_even hp hisOdd]
    simp
  · have hisOdd : p.isOdd = true := by simp [Affine.isOdd, h1]
    have ht3 : ((2 ||| p.y.isOdd).toUInt8 : UInt8) = 3 := by rw [h1]; rfl
    rw [ht3, parseXOnly_xBytes hp, hisOdd]
    simp [Affine.neg_neg hp]

/-! ## Generator order `N` and prime-order subgroup algebra -/

private def rAdd (p q : F × F × F) : F × F × F :=
  (RX p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2,
   RY p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2,
   RZ p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2)

private def rSmul (k : Nat) (g : F × F × F) : F × F × F :=
  (List.range 256).reverse.foldl
    (fun r i => if k.testBit i then rAdd (rAdd r r) g else rAdd r r)
    (0, 1, 0)

private theorem rSmul_rep (k : Nat) :
    RepF (rSmul k (Spec.Gx, Spec.Gy, 1)).1
      (rSmul k (Spec.Gx, Spec.Gy, 1)).2.1
      (rSmul k (Spec.Gx, Spec.Gy, 1)).2.2
      (Spec.smul k Spec.G) := by
  dsimp only [rSmul, Spec.smul]
  have hg : RepF Spec.Gx Spec.Gy 1 Spec.G :=
    ⟨1, by decide, by decide, by decide⟩
  have hinf : RepF 0 1 0 .inf := ⟨rfl, rfl, by decide⟩
  generalize (List.range 256).reverse = bits
  suffices ∀ (acc : F × F × F) (pt : Spec.Point), OnCurve pt → RepF acc.1 acc.2.1 acc.2.2 pt →
      let out := bits.foldl (fun r i => if k.testBit i then rAdd (rAdd r r) (Spec.Gx, Spec.Gy, 1) else rAdd r r) acc
      RepF out.1 out.2.1 out.2.2 (bits.foldl (fun r i => if k.testBit i then Spec.add (Spec.add r r) Spec.G else Spec.add r r) pt) from
    this (0, 1, 0) .inf trivial hinf
  induction bits with
  | nil => intro acc pt _ hrep; exact hrep
  | cons i rest ih =>
    intro acc pt hpt hrep
    simp only [List.foldl_cons]
    have hd := formulas_add hpt hpt hrep hrep
    have hcd := Spec.add_onCurve hpt hpt
    split
    · exact ih _ _ (Spec.add_onCurve hcd Spec.G_onCurve) (formulas_add hcd Spec.G_onCurve hd hg)
    · exact ih _ _ hcd hd

private theorem rSmul_N_z : (rSmul Spec.N (Spec.Gx, Spec.Gy, 1)).2.2 = 0 := by decide +kernel

private theorem smul_G_eq_inf_of_rSmul_z (n : Nat) (hz : (rSmul n (Spec.Gx, Spec.Gy, 1)).2.2 = 0) :
    Spec.smul n Spec.G = .inf := by
  have hrep := rSmul_rep n
  cases h : Spec.smul n Spec.G with
  | inf => rfl
  | pt x y =>
    rw [h] at hrep
    obtain ⟨w, hw, _⟩ := hrep
    exact absurd hz (ne_zero_of_mul_eq_one hw)

/-- **`N · G = .inf` in the curve specification.** -/
theorem smul_N_G : Spec.smul Spec.N Spec.G = .inf :=
  smul_G_eq_inf_of_rSmul_z Spec.N rSmul_N_z

theorem nsmul_N_G : Spec.nsmul Spec.N Spec.G = .inf := by
  rw [← Spec.smul_eq_nsmul Spec.N (by decide) Spec.G_onCurve]
  exact smul_N_G

theorem nsmul_mod_N (k : Nat) : Spec.nsmul k Spec.G = Spec.nsmul (k % Spec.N) Spec.G := by
  conv => lhs; rw [← Nat.div_add_mod k Spec.N, Nat.mul_comm Spec.N (k / Spec.N)]
  rw [Spec.nsmul_add _ _ Spec.G_onCurve, Spec.nsmul_mul _ _ Spec.G_onCurve, nsmul_N_G,
      Spec.nsmul_inf, Spec.inf_add]

/-- **Prime generator order `N`:** no scalar `0 < d < N` sends `G` to `.inf`. -/
theorem nsmul_G_ne_inf {d : Nat} (h0 : 0 < d) (hN : d < Spec.N) : Spec.nsmul d Spec.G ≠ .inf := by
  intro hinf
  have hnd : ¬ Spec.N ∣ d := fun hdvd => absurd (Nat.le_of_dvd h0 hdvd) (by omega)
  have hcop : Nat.gcd d Spec.N = 1 := by
    rw [Nat.gcd_comm]
    exact Secp.Primes.prime_coprime_of_not_dvd Secp.Primes.N_prime hnd
  obtain ⟨u, v, hbez⟩ := Secp.Primes.bezout_pos hcop h0 (by decide)
  have hlhs : Spec.nsmul (u * d) Spec.G = .inf := by
    rw [Spec.nsmul_mul u d Spec.G_onCurve, hinf, Spec.nsmul_inf]
  have hrhs : Spec.nsmul (1 + v * Spec.N) Spec.G = Spec.G := by
    rw [Spec.nsmul_add 1 (v * Spec.N) Spec.G_onCurve, Spec.nsmul_one,
        Spec.nsmul_mul v Spec.N Spec.G_onCurve, nsmul_N_G, Spec.nsmul_inf, Spec.add_inf]
  rw [hbez, hrhs] at hlhs
  exact absurd hlhs (by decide)

theorem smul_G_ne_inf {d : Nat} (h0 : 0 < d) (hN : d < Spec.N) : Spec.smul d Spec.G ≠ .inf := by
  rw [Spec.smul_eq_nsmul d (Nat.lt_trans hN (by decide)) Spec.G_onCurve]
  exact nsmul_G_ne_inf h0 hN

theorem smul_neg_G {d : Nat} (h0 : 0 < d) (hN : d < Spec.N) :
    Spec.smul (Spec.N - d) Spec.G = Spec.neg (Spec.smul d Spec.G) := by
  have hlt256 : Spec.N < 2 ^ 256 := by decide
  have hsub_lt : Spec.N - d < Spec.N := by omega
  rw [Spec.smul_eq_nsmul (Spec.N - d) (Nat.lt_trans hsub_lt hlt256) Spec.G_onCurve,
      Spec.smul_eq_nsmul d (Nat.lt_trans hN hlt256) Spec.G_onCurve]
  apply (Spec.add_eq_inf_iff (Spec.nsmul_onCurve d Spec.G_onCurve)
    (Spec.nsmul_onCurve (Spec.N - d) Spec.G_onCurve)).mp
  rw [← Spec.nsmul_add d (Spec.N - d) Spec.G_onCurve, show d + (Spec.N - d) = Spec.N by omega]
  exact nsmul_N_G

theorem toAffine?_complete {pt : Point} {x y : F} (hcurve : OnCurve (.pt x y)) (hrep : Rep pt (.pt x y)) :
    ∃ q, pt.toAffine? = some q ∧ q.spec = .pt x y ∧ q.Good := by
  obtain ⟨hx, hy, hflag, vx, vy⟩ := affine_point hrep
  unfold Point.toAffine?
  generalize pt.affine = t at hx hy hflag vx vy ⊢
  simp +zetaHave only
  rw [hflag]
  simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, ?_, vx, vy, ?_⟩
  · simp only [Affine.spec, hx, hy]
  · show t.2.1.toF * t.2.1.toF = t.1.toF * t.1.toF * t.1.toF + 7
    rw [hx, hy]
    exact hcurve

theorem publicPoint_complete {d : Sc} (h0 : 0 < d.toNat) (hN : d.toNat < N) :
    ∃ q, publicPoint d = some q ∧ q.spec = Spec.smul d.toNat Spec.G ∧ q.Good := by
  have hne := smul_G_ne_inf h0 (N_eq ▸ hN)
  have hcurve := Spec.smul_onCurve d.toNat Spec.G_onCurve
  cases hpt : Spec.smul d.toNat Spec.G with
  | inf => exact absurd hpt hne
  | pt x y =>
    rw [hpt] at hcurve
    have hrep := hpt ▸ mulGenerator_rep d
    obtain ⟨q, hq, hspec, hgood⟩ := toAffine?_complete hcurve hrep
    exact ⟨q, hq, hspec, hgood⟩

theorem publicKey_complete {secret : ByteArray} (hsz : secret.size = 32)
    (h0 : 0 < Secp.fromBE secret) (hN : Secp.fromBE secret < N) :
    ∃ x y : F, Spec.smul (Secp.fromBE secret) Spec.G = .pt x y ∧
      publicKey secret = some (Secp.toBE32 x.val, if y.val % 2 = 1 then 1 else 0) := by
  have hne := smul_G_ne_inf h0 (N_eq ▸ hN)
  cases hpt : Spec.smul (Secp.fromBE secret) Spec.G with
  | inf => exact absurd hpt hne
  | pt x y => exact ⟨x, y, rfl, publicKey_spec secret hsz h0 hN hpt⟩

/-! ## Unconditional BIP 340 signing completeness -/

private theorem publicPoint_coords {s : Sc} {p : Affine} (hp : publicPoint s = some p) :
    p.x = (Point.mulGenerator s).affine.1 ∧ p.y = (Point.mulGenerator s).affine.2.1 := by
  unfold publicPoint Point.toAffine? at hp
  generalize (Point.mulGenerator s).affine = coords at hp ⊢
  simp +zetaHave only at hp
  by_cases hc : (coords.2.2 == 1) = true
  · simp [hc] at hp
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hp
    rw [← hp]
    exact ⟨rfl, rfl⟩

private theorem negIf_smul_even {s : Sc} (h0 : 0 < s.toNat) (hN : s.toNat < N) :
    ∃ q : Affine,
      q.x = (Point.mulGenerator s).affine.1 ∧
      q.Good ∧
      q.isOdd = false ∧
      0 < (Sc.negIf (Point.mulGenerator s).affine.2.1.isOdd s).toNat ∧
      (Sc.negIf (Point.mulGenerator s).affine.2.1.isOdd s).toNat < N ∧
      q.spec = Spec.nsmul (Sc.negIf (Point.mulGenerator s).affine.2.1.isOdd s).toNat Spec.G := by
  obtain ⟨p, hp, hpspec, hpgood⟩ := publicPoint_complete h0 hN
  have hp_aff := publicPoint_coords hp
  let q := if p.isOdd then p.neg else p
  obtain ⟨qgood, qx, _, qeven⟩ := Affine.evenPartner_good hpgood
  have hisOdd_eq : (Point.mulGenerator s).affine.2.1.isOdd = p.y.isOdd := by rw [hp_aff.2]
  have hlt256 : N < 2 ^ 256 := by decide
  refine ⟨q, qx.trans hp_aff.1, qgood, qeven, ?_, ?_, ?_⟩
  · rw [hisOdd_eq]
    obtain ⟨hnat, _⟩ := negIf_parity s hN p.y p.y.toNat rfl
    rw [hnat]
    by_cases hodd : p.y.toNat % 2 = 1
    · simp only [hodd, ↓reduceIte, Secp.negN, ← N_eq]
      have hsub : (N - s.toNat) % N = N - s.toNat := Nat.mod_eq_of_lt (by omega)
      rw [hsub]; omega
    · simp only [hodd, ↓reduceIte]; exact h0
  · rw [hisOdd_eq]
    exact (negIf_parity s hN p.y p.y.toNat rfl).2
  · rw [hisOdd_eq]
    obtain ⟨hnat, _⟩ := negIf_parity s hN p.y p.y.toNat rfl
    have parity := Fe.isOdd_spec p.y
    by_cases hodd : p.y.toNat % 2 = 1
    · have hp_isOdd : p.isOdd = true := by
        simp only [Affine.isOdd, beq_iff_eq]
        exact UInt64.toNat_inj.mp (by rw [parity, hodd]; rfl)
      have hq_spec : q.spec = Spec.neg p.spec := by
        dsimp only [q]; rw [hp_isOdd]; simp only [↓reduceIte, Affine.spec, Affine.neg, Spec.neg]
        rw [toF_neg _ hpgood.2.1]
      rw [hq_spec, hpspec, hnat]
      simp only [hodd, ↓reduceIte, Secp.negN]
      have hsub : (Spec.N - s.toNat) % Spec.N = Spec.N - s.toNat := by
        rw [← N_eq]; exact Nat.mod_eq_of_lt (by omega)
      have hsub_lt : Spec.N - s.toNat < Spec.N := by rw [← N_eq]; omega
      rw [hsub, ← Spec.smul_eq_nsmul (Spec.N - s.toNat)
        (Nat.lt_trans hsub_lt (by decide)) Spec.G_onCurve]
      exact (smul_neg_G h0 (N_eq ▸ hN)).symm
    · have hp_isOdd : p.isOdd = false := by
        simp only [Affine.isOdd, beq_eq_false_iff_ne]
        intro hc; apply hodd; rw [← parity, hc]; rfl
      have hq_eq : q = p := by dsimp [q]; rw [hp_isOdd]; rfl
      rw [hq_eq, hpspec, hnat]
      simp only [hodd, ↓reduceIte]
      exact Spec.smul_eq_nsmul s.toNat (Nat.lt_trans hN hlt256) Spec.G_onCurve

private theorem filter_some_eq {α : Type} (p : α → Bool) (x : α) :
    Option.filter p (some x) = if p x then some x else none := rfl

private theorem any_some_eq {α : Type} (p : α → Bool) (x : α) :
    (some x).any p = p x := rfl

private theorem verify_eq_of_parts {sig msg key : ByteArray} {p : Affine} {r : Fe} {s : Sc}
    (hsz : sig.size = 64)
    (hp : parseXOnly key = some p)
    (hr : Fe.ofBytes? (sig.extract 0 32) = some r)
    (hs : scalar? (sig.extract 32 64) = some s) :
    verify sig msg key =
      ((Point.add (Point.mulPublic s Point.generator)
        (Point.mulPublic (Sc.ofBytes (Sha256.tagged "BIP0340/challenge" (r.bytes ++ p.x.bytes ++ msg))) p.point).neg
        ).toAffine?.filter fun sum => !sum.isOdd && Fe.same sum.x r).isSome := by
  unfold verify
  rw [hsz, beq_self_eq_true, Bool.true_and, hp, bind_some_eq, hr, bind_some_eq, hs, bind_some_eq]

/-- **BIP 340 signing completeness:** every signature `sign` returns verifies under the signer's own public key. -/
theorem verify_sign {secret message aux sig : ByteArray}
    (h : sign secret message aux = some sig) :
    ∃ key, publicKey secret = some key ∧ verify sig message key.1 = true := by
  unfold sign at h
  by_cases hsz : (secret.size != 32 || aux.size != 32) = true
  · simp [hsz] at h
  have hsz_f : (secret.size != 32 || aux.size != 32) = false := Bool.not_eq_true _ ▸ hsz
  rw [hsz_f] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have hsec_sz : secret.size = 32 := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hsz_f; exact hsz_f.1
  generalize hraw : signRaw secret message aux = res at h
  obtain ⟨sigOut, okBit⟩ := res
  dsimp only at h
  by_cases hok_eq : (okBit == 1) = true
  · simp only [hok_eq, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp only [beq_iff_eq] at hok_eq
    subst hok_eq
    -- Unpack `signRaw` without duplicating `(Point.mulGenerator _).affine`
    unfold signRaw at hraw
    generalize hd0 : Sc.ofBytes secret = d0 at hraw
    simp +zetaHave only at hraw
    generalize haffD : (Point.mulGenerator d0).affine = affD at hraw
    obtain ⟨px, py, pzFlag⟩ := affD
    dsimp only at hraw
    generalize hd : Sc.negIf py.isOdd d0 = d at hraw
    generalize hk0 : Sc.ofBytes (Sha256.tagged "BIP0340/nonce"
      (xor32 d.bytes (Sha256.tagged "BIP0340/aux" aux) ++ px.bytes ++ message)) = k0 at hraw
    generalize haffK : (Point.mulGenerator k0).affine = affK at hraw
    obtain ⟨rx, ry, rzFlag⟩ := affK
    dsimp only at hraw
    generalize hk : Sc.negIf ry.isOdd k0 = k at hraw
    generalize he : Sc.ofBytes (Sha256.tagged "BIP0340/challenge" (rx.bytes ++ px.bytes ++ message)) = e at hraw
    generalize hs : Sc.add k (Sc.mul e d) = s at hraw
    simp only [Prod.mk.injEq] at hraw
    obtain ⟨hsig_def, hok⟩ := hraw
    subst hsig_def
    have hkey1 : Sc.isKey secret = 1 := by
      rcases (by rw [Sc.isKey_spec secret hsec_sz]; split <;> simp : Sc.isKey secret = 0 ∨ Sc.isKey secret = 1) with h0 | h1
      · rw [h0, UInt64.zero_and] at hok; exact absurd hok (by decide)
      · exact h1
    have hsec_range : 0 < Secp.fromBE secret ∧ Secp.fromBE secret < N := by
      rw [Sc.isKey_spec secret hsec_sz] at hkey1
      split at hkey1
      · assumption
      · exact absurd hkey1 (by decide)
    have hd0_nat : d0.toNat = Secp.fromBE secret := by
      rw [← hd0, Sc.ofBytes_spec secret hsec_sz, Nat.mod_eq_of_lt hsec_range.2]
    have hd0_pos : 0 < d0.toNat := hd0_nat ▸ hsec_range.1
    have hd0_lt : d0.toNat < N := hd0_nat ▸ hsec_range.2
    obtain ⟨P_ev, hPx, hPgood, hPeven, _, hd_lt, hPspec⟩ := negIf_smul_even hd0_pos hd0_lt
    rw [haffD] at hPx hd_lt hPspec
    dsimp only at hPx hd_lt hPspec
    rw [hd] at hd_lt hPspec
    have hk0_lt : k0.toNat < N := by
      rw [← hk0, Sc.ofBytes_spec _ (tagged_size _ _)]; exact Nat.mod_lt _ (by decide)
    have hk0_pos : 0 < k0.toNat := by
      have b_kz : (k0.isZero ^^^ 1) = 0 ∨ (k0.isZero ^^^ 1) = 1 := by
        rw [Sc.isZero_spec]; split <;> decide
      have hk0_flag : k0.isZero ^^^ 1 = 1 := by
        rw [hkey1] at hok
        rcases b_kz with hz | ho
        · rw [hz] at hok; exact absurd hok (by decide)
        · exact ho
      rw [Sc.isZero_spec] at hk0_flag
      by_cases hk0z : k0.toNat = 0
      · simp [hk0z] at hk0_flag
      · omega
    obtain ⟨R_ev, hRx, hRgood, hReven, _, hk_lt, hRspec⟩ := negIf_smul_even hk0_pos hk0_lt
    rw [haffK] at hRx hk_lt hRspec
    dsimp only at hRx hk_lt hRspec
    rw [hk] at hk_lt hRspec
    -- 1. `publicKey secret` succeeds and returns `px.bytes`
    obtain ⟨pxF, pyF, hpt_sec, hpk⟩ := publicKey_complete hsec_sz hsec_range.1 hsec_range.2
    have hpk_bytes : Secp.toBE32 pxF.val = px.bytes := by
      have rep := mulGenerator_rep d0
      rw [hd0_nat, hpt_sec] at rep
      obtain ⟨hx, _, _, vx, _⟩ := affine_point rep
      rw [haffD] at hx vx
      dsimp only at hx vx
      rw [← Fe.toNat_of_toF vx hx, ← Fe.bytes_spec]
    refine ⟨(px.bytes, if pyF.val % 2 = 1 then 1 else 0), hpk_bytes ▸ hpk, ?_⟩
    -- 2. Evaluate `verify` on `rx.bytes ++ s.bytes`, `message`, `px.bytes`
    have hrx_sz : rx.bytes.size = 32 := Fe.bytes_size rx
    have hs_sz : s.bytes.size = 32 := Sc.bytes_size s
    have hsig_sz : (rx.bytes ++ s.bytes).size = 64 := by rw [ByteArray.size_append, hrx_sz, hs_sz]
    have hex0 : (rx.bytes ++ s.bytes).extract 0 32 = rx.bytes := hrx_sz ▸ extract_append_left rx.bytes s.bytes
    have hex1 : (rx.bytes ++ s.bytes).extract 32 64 = s.bytes := by
      have hslice := extract_append_right rx.bytes s.bytes
      rw [hrx_sz, hs_sz] at hslice
      exact hslice
    have hparse_pk : parseXOnly px.bytes = some P_ev := by
      rw [← hPx]; exact parseXOnly_xBytes_even hPgood hPeven
    have hrx_fe : Fe.ofBytes? rx.bytes = some R_ev.x := by
      rw [← hRx]; exact Fe.ofBytes?_bytes hRgood.1
    have hs_lt : s.toNat < N := by
      rw [← hs, Sc.add_spec k (Sc.mul e d) hk_lt (Sc.mul_lt e d)]
      exact Nat.mod_lt _ (by decide)
    have hs_sc : scalar? s.bytes = some s := scalar?_bytes hs_lt
    rw [verify_eq_of_parts hsig_sz hparse_pk (by rw [hex0]; exact hrx_fe) (by rw [hex1]; exact hs_sc)]
    have he_eq : Sc.ofBytes (Sha256.tagged "BIP0340/challenge" (R_ev.x.bytes ++ P_ev.x.bytes ++ message)) = e := by
      rw [hRx, hPx, he]
    rw [he_eq]
    -- 3. Group equation: `s · G - e · P_ev = R_ev`
    have hlt256 : N < 2 ^ 256 := by decide
    have he_lt : e.toNat < N := by
      rw [← he, Sc.ofBytes_spec _ (tagged_size _ _)]; exact Nat.mod_lt _ (by decide)
    have hsum_spec : Spec.add (Spec.smul s.toNat Spec.G) (Spec.neg (Spec.smul e.toNat P_ev.spec)) = R_ev.spec := by
      rw [Spec.smul_eq_nsmul s.toNat (Nat.lt_trans hs_lt hlt256) Spec.G_onCurve,
          Spec.smul_eq_nsmul e.toNat (Nat.lt_trans he_lt hlt256) hPgood.2.2,
          hPspec, ← Spec.nsmul_mul e.toNat d.toNat Spec.G_onCurve]
      have hs_val : s.toNat = (k.toNat + e.toNat * d.toNat) % Spec.N := by
        rw [← hs, ← N_eq, Sc.add_spec k (Sc.mul e d) hk_lt (Sc.mul_lt e d), Sc.mul_spec, Nat.add_mod_mod]
      rw [hs_val, ← nsmul_mod_N (k.toNat + e.toNat * d.toNat),
          Spec.nsmul_add k.toNat (e.toNat * d.toNat) Spec.G_onCurve,
          Spec.add_assoc (Spec.nsmul_onCurve k.toNat Spec.G_onCurve)
            (Spec.nsmul_onCurve (e.toNat * d.toNat) Spec.G_onCurve)
            (Spec.neg_onCurve (Spec.nsmul_onCurve (e.toNat * d.toNat) Spec.G_onCurve)),
          Spec.add_neg_self (Spec.nsmul_onCurve (e.toNat * d.toNat) Spec.G_onCurve),
          Spec.add_inf, ← hRspec]
    have hrep_sum : Rep (Point.add (Point.mulPublic s Point.generator) (Point.mulPublic e P_ev.point).neg) R_ev.spec := by
      rw [← hsum_spec]
      exact rep_add (Spec.smul_onCurve s.toNat Spec.G_onCurve)
        (Spec.neg_onCurve (Spec.smul_onCurve e.toNat hPgood.2.2))
        (mulPublic_rep s Spec.G_onCurve rep_generator)
        (rep_neg (mulPublic_rep e hPgood.2.2 (Affine.rep hPgood)))
    obtain ⟨sumAff, htoAff, hsum_aff_spec, hsum_good⟩ := toAffine?_complete hRgood.2.2 hrep_sum
    have hsum_eq : sumAff = R_ev := Affine.ext_spec hsum_good hRgood hsum_aff_spec
    rw [htoAff, hsum_eq, filter_some_eq]
    simp only [hReven, Bool.not_false, Fe.same_refl, Bool.and_self, ↓reduceIte, Option.isSome_some]
  · simp [hok_eq] at h

/-- **`signVerified` is extensionally identical to `sign`.** -/
theorem signVerified_eq_sign (secret message aux : ByteArray) :
    signVerified secret message aux = sign secret message aux := by
  unfold signVerified
  cases hs : sign secret message aux with
  | none => rfl
  | some sig =>
    obtain ⟨key, hpk, hver⟩ := verify_sign hs
    rw [filter_some_eq, hpk, any_some_eq, hver]
    rfl

/-! ## Unconditional ECDSA signing completeness -/

private theorem ecdsa_verify_eq_of_parts {sig digest key : ByteArray} {q : Affine} {r s : Sc}
    (hsz : sig.size = 64) (hdig : digest.size = 32)
    (hr_eq : Sc.ofBytes (sig.extract 0 32) = r)
    (hs_eq : Sc.ofBytes (sig.extract 32 64) = s)
    (hr_key : Sc.isKey (sig.extract 0 32) = 1)
    (hs_key : Sc.isKey (sig.extract 32 64) = 1)
    (hs_low : Sc.isHigh s = 0)
    (hsw : Sc.mul s (Sc.inv s) = Sc.one)
    (hq : parseCompressed key = some q) :
    Ecdsa.verify sig digest key =
      ((Point.add (Point.mulPublic (Sc.mul (Sc.ofBytes digest) (Sc.inv s)) Point.generator)
        (Point.mulPublic (Sc.mul r (Sc.inv s)) q.point)).toAffine?.filter fun sum =>
          Sc.same (Sc.reduceOnce sum.x.a0 sum.x.a1 sum.x.a2 sum.x.a3 0) r).isSome := by
  unfold Ecdsa.verify
  dsimp only
  rw [hr_eq, hs_eq]
  generalize Sc.inv s = w at hsw ⊢
  simp +zetaHave only [hsz, hdig, hr_key, hs_key, hs_low, hsw, Sc.same_refl, beq_self_eq_true, Bool.true_and]
  rw [hq, bind_some_eq]

private theorem sub_prod_id (n a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    (n - a) * (n - b) + n * (a + b) = n * n + a * b := by
  have hu : a + (n - a) = n := Nat.add_sub_of_le ha
  have hv : b + (n - b) = n := Nat.add_sub_of_le hb
  generalize n - a = u at hu ⊢
  generalize n - b = v at hv ⊢
  grind

/-- **ECDSA signing completeness:** every signature `Ecdsa.sign` returns verifies under the signer's compressed
public key (and round-trips through strict BIP 66 DER). -/
theorem Ecdsa.verify_sign {secret digest aux sig : ByteArray}
    (h : Ecdsa.sign secret digest aux = some sig) :
    ∃ key, publicPoint (Sc.ofBytes secret) = some key ∧
      Ecdsa.verify sig digest key.compressed = true ∧
      Secp.Ecdsa.parseDer (Secp.Ecdsa.der sig) = some sig := by
  unfold Ecdsa.sign at h
  by_cases hsz : (secret.size != 32 || digest.size != 32 || aux.size != 32) = true
  · simp [hsz] at h
  have hsz_f : (secret.size != 32 || digest.size != 32 || aux.size != 32) = false := Bool.not_eq_true _ ▸ hsz
  rw [hsz_f] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have hsec_sz : secret.size = 32 := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hsz_f; exact hsz_f.1.1
  have hdig_sz : digest.size = 32 := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hsz_f; exact hsz_f.1.2
  generalize hraw : Ecdsa.signRaw secret digest aux = res at h
  obtain ⟨sigOut, okBit⟩ := res
  dsimp only at h
  by_cases hok_eq : (okBit == 1) = true
  · simp only [hok_eq, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp only [beq_iff_eq] at hok_eq
    subst hok_eq
    -- Unpack `Ecdsa.signRaw` via `generalize` so `(Point.mulGenerator _).affine` is never duplicated or unfolded
    unfold Ecdsa.signRaw at hraw
    generalize hd : Sc.ofBytes secret = d at hraw
    generalize hz : Sc.ofBytes digest = z at hraw
    simp +zetaHave only at hraw
    generalize hk : Sc.ofBytes (Sha256.tagged "winnow/ecdsa/nonce"
      (xor32 d.bytes (Sha256.tagged "winnow/ecdsa/aux" aux) ++ digest)) = k at hraw
    generalize haffK : (Point.mulGenerator k).affine = affK at hraw
    obtain ⟨rx, ry, rzFlag⟩ := affK
    dsimp only at hraw
    generalize hr : Sc.reduceOnce rx.a0 rx.a1 rx.a2 rx.a3 0 = r at hraw
    generalize hs0 : Sc.mul (Sc.inv k) (Sc.add z (Sc.mul r d)) = s0 at hraw
    generalize hs : Sc.negIf (Sc.isHigh s0) s0 = s at hraw
    simp only [Prod.mk.injEq] at hraw
    obtain ⟨hsig_def, hok⟩ := hraw
    subst hsig_def
    have bit01 {u : UInt64} (hu : u = 0 ∨ u = 1) {v : UInt64} (hand : u &&& v = 1) : u = 1 := by
      rcases hu with rfl | rfl
      · rw [UInt64.zero_and] at hand; exact absurd hand (by decide)
      · rfl
    have bit01_r {v : UInt64} (hv : v = 0 ∨ v = 1) (hand : 1 &&& v = 1) : v = 1 := by
      rcases hv with rfl | rfl
      · exact absurd hand (by decide)
      · rfl
    have b_key : Sc.isKey secret = 0 ∨ Sc.isKey secret = 1 := by
      rw [Sc.isKey_spec secret hsec_sz]; split <;> simp
    have b_kz : (k.isZero ^^^ 1) = 0 ∨ (k.isZero ^^^ 1) = 1 := by
      rw [Sc.isZero_spec]; split <;> decide
    have b_rz : (r.isZero ^^^ 1) = 0 ∨ (r.isZero ^^^ 1) = 1 := by
      rw [Sc.isZero_spec]; split <;> decide
    have b_sz : (s.isZero ^^^ 1) = 0 ∨ (s.isZero ^^^ 1) = 1 := by
      rw [Sc.isZero_spec]; split <;> decide
    have b_12 : (Sc.isKey secret &&& (k.isZero ^^^ 1)) = 0 ∨ (Sc.isKey secret &&& (k.isZero ^^^ 1)) = 1 := by
      rcases b_key with h1 | h1 <;> rcases b_kz with h2 | h2 <;> (rw [h1, h2]; decide)
    have b_123 : (Sc.isKey secret &&& (k.isZero ^^^ 1) &&& (r.isZero ^^^ 1)) = 0 ∨
        (Sc.isKey secret &&& (k.isZero ^^^ 1) &&& (r.isZero ^^^ 1)) = 1 := by
      rcases b_12 with h1 | h1 <;> rcases b_rz with h2 | h2 <;> (rw [h1, h2]; decide)
    have h123 : Sc.isKey secret &&& (k.isZero ^^^ 1) &&& (r.isZero ^^^ 1) = 1 := bit01 b_123 hok
    have hs_nz_flag : s.isZero ^^^ 1 = 1 := bit01_r b_sz (by rw [h123] at hok; exact hok)
    have h12 : Sc.isKey secret &&& (k.isZero ^^^ 1) = 1 := bit01 b_12 h123
    have hr_nz_flag : r.isZero ^^^ 1 = 1 := bit01_r b_rz (by rw [h12] at h123; exact h123)
    have hkey1 : Sc.isKey secret = 1 := bit01 b_key h12
    have hk_nz_flag : k.isZero ^^^ 1 = 1 := bit01_r b_kz (by rw [hkey1] at h12; exact h12)
    -- Ranges of `d`, `k`, `r`, `s0`, `s`
    have hsec_range : 0 < Secp.fromBE secret ∧ Secp.fromBE secret < N := by
      rw [Sc.isKey_spec secret hsec_sz] at hkey1
      split at hkey1
      · assumption
      · exact absurd hkey1 (by decide)
    have hd_nat : d.toNat = Secp.fromBE secret := by
      rw [← hd, Sc.ofBytes_spec secret hsec_sz, Nat.mod_eq_of_lt hsec_range.2]
    have hd_pos : 0 < d.toNat := hd_nat ▸ hsec_range.1
    have hd_lt : d.toNat < N := hd_nat ▸ hsec_range.2
    have hk_lt : k.toNat < N := by
      rw [← hk, Sc.ofBytes_spec _ (tagged_size _ _)]; exact Nat.mod_lt _ (by decide)
    have hk_pos : 0 < k.toNat := by
      rw [Sc.isZero_spec] at hk_nz_flag
      by_cases hkz : k.toNat = 0
      · simp [hkz] at hk_nz_flag
      · omega
    have hr_mod : r.toNat = rx.toNat % N := by rw [← hr]; exact reduceOnce_mod rx.a0 rx.a1 rx.a2 rx.a3
    have hr_lt : r.toNat < N := by rw [hr_mod]; exact Nat.mod_lt _ (by decide)
    have hr_pos : 0 < r.toNat := by
      rw [Sc.isZero_spec] at hr_nz_flag
      by_cases hrz : r.toNat = 0
      · simp [hrz] at hr_nz_flag
      · omega
    have hs0_lt : s0.toNat < N := by rw [← hs0]; exact Sc.mul_lt _ _
    have hs_pos : 0 < s.toNat := by
      rw [Sc.isZero_spec] at hs_nz_flag
      by_cases hsz0 : s.toNat = 0
      · simp [hsz0] at hs_nz_flag
      · omega
    have hs_low_and_lt : s.toNat ≤ N / 2 ∧ s.toNat < N := by
      have hN_odd : 2 * (N / 2) + 1 = N := by decide
      by_cases hhigh : s0.toNat > N / 2
      · have hisH : Sc.isHigh s0 = 1 := by rw [Sc.isHigh_spec]; simp [hhigh]
        have hs_val : s.toNat = N - s0.toNat := by
          rw [← hs, hisH, Sc.negIf_one, Sc.neg_spec s0 hs0_lt]
          exact Nat.mod_eq_of_lt (by omega)
        omega
      · have hisH : Sc.isHigh s0 = 0 := by rw [Sc.isHigh_spec]; simp [hhigh]
        have hs_val : s = s0 := by rw [← hs, hisH, Sc.negIf_zero]
        rw [hs_val]; omega
    -- Public key and DER round-trip
    obtain ⟨Q, hQ, hQspec, hQgood⟩ := publicPoint_complete hd_pos hd_lt
    have hr_sz : r.bytes.size = 32 := Sc.bytes_size r
    have hs_sz : s.bytes.size = 32 := Sc.bytes_size s
    have hsig_sz : (r.bytes ++ s.bytes).size = 64 := by rw [ByteArray.size_append, hr_sz, hs_sz]
    refine ⟨Q, hd ▸ hQ, ?_, Secp.Ecdsa.parseDer_der hsig_sz⟩
    -- Unfold `Ecdsa.verify`
    have hex0 : (r.bytes ++ s.bytes).extract 0 32 = r.bytes := hr_sz ▸ extract_append_left r.bytes s.bytes
    have hex1 : (r.bytes ++ s.bytes).extract 32 64 = s.bytes := by
      have hslice := extract_append_right r.bytes s.bytes
      rw [hr_sz, hs_sz] at hslice
      exact hslice
    have hr_key : Sc.isKey r.bytes = 1 := by
      rw [Sc.isKey_spec _ hr_sz, Sc.fromBE_bytes]; simp [hr_pos, hr_lt]
    have hs_key : Sc.isKey s.bytes = 1 := by
      rw [Sc.isKey_spec _ hs_sz, Sc.fromBE_bytes]; simp [hs_pos, hs_low_and_lt.2]
    have hs_not_high : Sc.isHigh s = 0 := by
      rw [Sc.isHigh_spec]; have := hs_low_and_lt.1; simp [show ¬ s.toNat > N / 2 by omega]
    generalize hw : Sc.inv s = w
    have hsw_one : Sc.mul s w = Sc.one := by
      apply Sc.toNat_inj
      rw [Sc.mul_spec, ← hw, Sc.inv_spec, Sc.one_toNat, N_eq, Nat.mul_mod_mod]
      apply Secp.Primes.power_inverse_N s.toNat
      rw [← N_eq, Nat.mod_eq_of_lt hs_low_and_lt.2]
      omega
    rw [ecdsa_verify_eq_of_parts (r := r) (s := s) hsig_sz hdig_sz
          (by rw [hex0]; exact Sc.ofBytes_bytes hr_lt)
          (by rw [hex1]; exact Sc.ofBytes_bytes hs_low_and_lt.2)
          (by rw [hex0]; exact hr_key)
          (by rw [hex1]; exact hs_key)
          hs_not_high
          (by rw [hw]; exact hsw_one)
          (parseCompressed_compressed hQgood),
        hz, hw]
    generalize hu1 : Sc.mul z w = u1
    generalize hu2 : Sc.mul r w = u2
    -- Group equation: `(z·w)·G + (r·w)·Q = ±(k·G)`
    have hz_lt : z.toNat < N := by
      rw [← hz, Sc.ofBytes_spec _ hdig_sz]; exact Nat.mod_lt _ (by decide)
    have hks0 : (k.toNat * s0.toNat) % N = (z.toNat + r.toNat * d.toNat) % N := by
      have hk_inv : (k.toNat * (Sc.inv k).toNat) % N = 1 := by
        rw [Sc.inv_spec, N_eq, Nat.mul_mod_mod]
        apply Secp.Primes.power_inverse_N k.toNat
        rw [← N_eq, Nat.mod_eq_of_lt hk_lt]; omega
      calc (k.toNat * s0.toNat) % N
          = (k.toNat * ((Sc.inv k).toNat * ((z.toNat + (r.toNat * d.toNat % N)) % N) % N)) % N := by
            rw [← hs0, Sc.mul_spec, Sc.add_spec z (Sc.mul r d) hz_lt (Sc.mul_lt r d), Sc.mul_spec]
        _ = ((k.toNat * (Sc.inv k).toNat) * ((z.toNat + r.toNat * d.toNat) % N)) % N := by
            rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.add_mod_mod]
        _ = ((k.toNat * (Sc.inv k).toNat) % N * ((z.toNat + r.toNat * d.toNat) % N)) % N := by
            rw [Nat.mul_mod (k.toNat * (Sc.inv k).toNat), Nat.mod_mod]
        _ = (z.toNat + r.toNat * d.toNat) % N := by
            rw [hk_inv, Nat.one_mul, Nat.mod_mod]
    have hsw_nat : (s.toNat * w.toNat) % N = 1 := by
      have := congrArg Sc.toNat hsw_one
      rw [Sc.mul_spec, Sc.one_toNat] at this
      exact this
    have hu_comb : (u1.toNat + u2.toNat * d.toNat) % N = ((z.toNat + r.toNat * d.toNat) * w.toNat) % N := by
      have hu1_nat : u1.toNat = z.toNat * w.toNat % N := by rw [← hu1]; exact Sc.mul_spec z w
      have hu2_nat : u2.toNat = r.toNat * w.toNat % N := by rw [← hu2]; exact Sc.mul_spec r w
      rw [hu1_nat, hu2_nat]
      calc (z.toNat * w.toNat % N + r.toNat * w.toNat % N * d.toNat) % N
          = (z.toNat * w.toNat % N + (r.toNat * w.toNat * d.toNat) % N) % N := by
            rw [Nat.add_mod (z.toNat * w.toNat % N), Nat.mod_mod,
                Nat.mul_mod (r.toNat * w.toNat % N) d.toNat N, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
        _ = (z.toNat * w.toNat + r.toNat * d.toNat * w.toNat) % N := by
            rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_right_comm r.toNat w.toNat d.toNat]
        _ = ((z.toNat + r.toNat * d.toNat) * w.toNat) % N := by rw [Nat.add_mul]
    obtain ⟨R, hR, hRspec, hRgood⟩ := publicPoint_complete hk_pos hk_lt
    have hRx_eq : R.x = rx := by
      have hc := (publicPoint_coords hR).1
      rw [haffK] at hc
      exact hc
    have hlt256 : N < 2 ^ 256 := by decide
    have hu1_lt : u1.toNat < N := hu1 ▸ Sc.mul_lt z w
    have hu2_lt : u2.toNat < N := hu2 ▸ Sc.mul_lt r w
    have hsum_lhs : Spec.add (Spec.smul u1.toNat Spec.G) (Spec.smul u2.toNat Q.spec) =
        Spec.nsmul ((u1.toNat + u2.toNat * d.toNat) % Spec.N) Spec.G := by
      rw [Spec.smul_eq_nsmul u1.toNat (Nat.lt_trans hu1_lt hlt256) Spec.G_onCurve,
          Spec.smul_eq_nsmul u2.toNat (Nat.lt_trans hu2_lt hlt256) hQgood.2.2,
          hQspec, Spec.smul_eq_nsmul d.toNat (Nat.lt_trans hd_lt hlt256) Spec.G_onCurve,
          ← Spec.nsmul_mul u2.toNat d.toNat Spec.G_onCurve,
          ← Spec.nsmul_add u1.toNat (u2.toNat * d.toNat) Spec.G_onCurve,
          nsmul_mod_N]
    -- Either `s = s0` (sum is `R`) or `s = N - s0` (sum is `R.neg`); both have `x = rx`!
    have htarget : ∃ T : Affine, T.Good ∧ T.x = rx ∧
        Spec.nsmul ((u1.toNat + u2.toNat * d.toNat) % Spec.N) Spec.G = T.spec := by
      by_cases hhigh : s0.toNat > N / 2
      · have hisH : Sc.isHigh s0 = 1 := by rw [Sc.isHigh_spec]; simp [hhigh]
        have hs_val : s.toNat = N - s0.toNat := by
          rw [← hs, hisH, Sc.negIf_one, Sc.neg_spec s0 hs0_lt]
          exact Nat.mod_eq_of_lt (by omega)
        have hneg_prod : ((N - k.toNat) * s.toNat) % N = (k.toNat * s0.toNat) % N := by
          rw [hs_val]
          have heq := sub_prod_id N k.toNat s0.toNat (Nat.le_of_lt hk_lt) (Nat.le_of_lt hs0_lt)
          have hm := congrArg (· % N) heq
          rw [Nat.add_mul_mod_self_left, Nat.add_comm (N * N), Nat.add_mul_mod_self_left] at hm
          exact hm
        have hu_eq : (u1.toNat + u2.toNat * d.toNat) % Spec.N = Spec.N - k.toNat := by
          have hk_sub_lt : N - k.toNat < N := by omega
          rw [← N_eq, hu_comb, ← Nat.mod_mul_mod, ← hks0, ← hneg_prod, Nat.mod_mul_mod,
              Nat.mul_assoc, ← Nat.mul_mod_mod _ (s.toNat * w.toNat), hsw_nat, Nat.mul_one,
              Nat.mod_eq_of_lt hk_sub_lt]
        refine ⟨R.neg, Affine.neg_good hRgood, hRx_eq, ?_⟩
        have hk_sub_spec : Spec.N - k.toNat < Spec.N := by rw [← N_eq]; omega
        rw [hu_eq, ← Spec.smul_eq_nsmul (Spec.N - k.toNat)
            (Nat.lt_trans hk_sub_spec (by decide)) Spec.G_onCurve,
            smul_neg_G hk_pos (N_eq ▸ hk_lt), ← hRspec]
        simp [Affine.spec, Affine.neg, Spec.neg, toF_neg _ hRgood.2.1]
      · have hisH : Sc.isHigh s0 = 0 := by rw [Sc.isHigh_spec]; simp [hhigh]
        have hs_val : s = s0 := by rw [← hs, hisH, Sc.negIf_zero]
        have hu_eq : (u1.toNat + u2.toNat * d.toNat) % Spec.N = k.toNat := by
          rw [← N_eq, hu_comb, ← Nat.mod_mul_mod, ← hks0, Nat.mod_mul_mod,
              ← hs_val, Nat.mul_assoc, ← Nat.mul_mod_mod _ (s.toNat * w.toNat), hsw_nat,
              Nat.mul_one, Nat.mod_eq_of_lt hk_lt]
        refine ⟨R, hRgood, hRx_eq, ?_⟩
        rw [hu_eq, ← Spec.smul_eq_nsmul k.toNat (Nat.lt_trans hk_lt hlt256) Spec.G_onCurve, hRspec]
    obtain ⟨T, hTgood, hTx, hTspec⟩ := htarget
    have hrep_sum : Rep (Point.add (Point.mulPublic u1 Point.generator) (Point.mulPublic u2 Q.point)) T.spec := by
      rw [← hTspec, ← hsum_lhs]
      exact rep_add (Spec.smul_onCurve u1.toNat Spec.G_onCurve) (Spec.smul_onCurve u2.toNat hQgood.2.2)
        (mulPublic_rep u1 Spec.G_onCurve rep_generator)
        (mulPublic_rep u2 hQgood.2.2 (Affine.rep hQgood))
    obtain ⟨sumAff, htoAff, hsum_spec, hsum_good⟩ := toAffine?_complete hTgood.2.2 hrep_sum
    have hsum_eq : sumAff = T := Affine.ext_spec hsum_good hTgood hsum_spec
    rw [htoAff, hsum_eq, filter_some_eq]
    simp only [hTx, hr, Sc.same_refl, ↓reduceIte, Option.isSome_some]
  · simp [hok_eq] at h

/-- **`Ecdsa.signVerified` is extensionally identical to `sign`.** -/
theorem Ecdsa.signVerified_eq_sign (secret digest aux : ByteArray) :
    Ecdsa.signVerified secret digest aux = Ecdsa.sign secret digest aux := by
  unfold Ecdsa.signVerified
  cases hs : Ecdsa.sign secret digest aux with
  | none => rfl
  | some sig =>
    obtain ⟨key, hpk, hver, _⟩ := Ecdsa.verify_sign hs
    rw [filter_some_eq, hpk, any_some_eq, hver]
    rfl

end SecpCt
