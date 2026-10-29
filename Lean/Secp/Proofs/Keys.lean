import Secp.Keys

/-! # What the key and signature functions compute, over the spec curve

Each theorem takes an answer the oracle gave and says what it is in terms of `Spec`: public keys
are `d·G`, parsed and lifted points lie on the curve with the stated x and parity, tweaks are
`t·G + K`, and `verify` accepts only when BIP340's equation holds on the spec curve. Those with a
`[FieldP]` premise rest on the one assumption, that `P` is prime. -/

namespace Secp
open Spec

theorem Gpt_toSpec : Gpt.toSpec = Spec.G := by
  simp only [Gpt, APoint.toSpec, Spec.G, Fq.toF_ofNat]
  congr 1 <;> apply Fin.ext <;> simp only [Nat.mod_eq_of_lt (Fin.isLt _)]

theorem mulG_spec [FieldP] {k : Nat} {q : APoint} (h : mulG k = .ok q) : q.toSpec = Spec.smul k Spec.G := by
  unfold mulG at h
  split at h
  · rename_i r hr; cases h; rw [← Gpt_toSpec]; exact smul?_spec hr
  · cases h

theorem mulPt_spec [FieldP] {k : Nat} {p q : APoint} (h : mulPt k p = .ok q) : q.toSpec = Spec.smul k p.toSpec := by
  unfold mulPt at h
  split at h
  · rename_i r hr; cases h; exact smul?_spec hr
  · cases h

theorem mulGAdd_spec [FieldP] {k : Nat} {p q : APoint} (h : mulGAdd k p = .ok q) :
    q.toSpec = Spec.add (Spec.smul k Spec.G) p.toSpec := by
  unfold mulGAdd at h
  split at h
  · rename_i r hr
    cases h
    rw [← Gpt_toSpec]
    exact toAffine?_spec (rep_add p (rep_fold k Gpt _ _ _ rep_inf)) hr
  · cases h

/-- A public key is `d·G`. -/
theorem pubOf_spec [FieldP] {d : Nat} {x y : Fq} (h : pubOf d = .ok (x, y)) :
    Spec.smul d Spec.G = .pt x.toF y.toF := by
  unfold pubOf at h
  cases hg : mulG d with
  | error e => simp [hg, bind, Except.bind] at h
  | ok q =>
    simp only [hg, bind, Except.bind] at h
    cases q with
    | inf => cases h
    | pt x' y' =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [← mulG_spec hg]; rfl

theorem pubOf_onCurve [FieldP] {d : Nat} {x y : Fq} (h : pubOf d = .ok (x, y)) :
    OnCurve (.pt x.toF y.toF) := by
  rw [← pubOf_spec h]; exact smul_onCurve d G_onCurve

/-! ## Parity -/

theorem P_odd : P % 2 = 1 := by decide

theorem Fq.neg_toNat (a : Fq) : (-a).toNat = (P - a.toNat) % P := by
  simp only [Fq.toNat_eq, Fq.toF_neg, Fin.neg_def]

theorem Fq.neg_toNat_of_pos {a : Fq} (h : 0 < a.toNat) : (-a).toNat = P - a.toNat := by
  rw [Fq.neg_toNat]
  have hlt : a.toNat < P := a.toF.isLt
  exact Nat.mod_eq_of_lt (by omega)

theorem Fq.isOdd_iff (a : Fq) : a.isOdd = true ↔ a.toNat % 2 = 1 := by
  simp [Fq.isOdd]

theorem Fq.isOdd_neg {a : Fq} (h : a.isOdd = true) : (-a).isOdd = false := by
  rw [Fq.isOdd_iff] at h
  have hpos : 0 < a.toNat := by omega
  have hlt : a.toNat < P := a.toF.isLt
  have := P_odd
  have e := Fq.neg_toNat_of_pos hpos
  cases hn : (-a).isOdd
  · rfl
  · rw [Fq.isOdd_iff, e] at hn; omega

theorem even_choice (y : Fq) : (if y.isOdd then -y else y).isOdd = false := by
  cases hy : y.isOdd
  · simp [hy]
  · simp only [ite_true]; exact Fq.isOdd_neg hy

theorem neg_sq (y : Fq) : (-y).toF * (-y).toF = y.toF * y.toF := by
  rw [Fq.toF_neg]; grind

/-! ## Points from bytes -/

/-- `lift_x`: the point has the requested x, lies on the curve, and its y is even.
No assumption about `P` is needed: the square root checks itself. -/
theorem liftX?_spec {n : Nat} {x y : Fq} (h : liftX? n = some (x, y)) :
    x.toF.val = n ∧ OnCurve (.pt x.toF y.toF) ∧ y.isOdd = false := by
  unfold liftX? at h
  split at h
  · rename_i hn
    simp only at h
    split at h
    · rename_i y' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hsq := Fq.sqrt?_spec hs
      refine ⟨?_, ?_, even_choice y'⟩
      · simp [Fq.toF_ofNat, Nat.mod_eq_of_lt hn]
      · show _ * _ = _
        have : (if y'.isOdd then -y' else y').toF * (if y'.isOdd then -y' else y').toF = y'.toF * y'.toF := by
          split
          · exact neg_sq y'
          · rfl
        rw [this, hsq]
        simp only [Fq.toF_add, Fq.toF_mul]
        rfl
    · cases h
  · cases h

/-- A parsed compressed key lies on the curve, with the encoded x and the parity its prefix names.
(The parity clause is vacuous only for y = 0, a point secp256k1 does not have: its order is odd.
That fact is not proven here, so it stays a disjunct.) -/
theorem parseCompressed_spec {b : ByteArray} {x y : Fq} (h : parseCompressed b = .ok (x, y)) :
    x.toF.val = fromBE (b.extract 1 33) ∧ OnCurve (.pt x.toF y.toF)
      ∧ (y.toF = 0 ∨ (y.isOdd = true ↔ b[0]! = 3)) := by
  unfold parseCompressed at h
  split at h
  · split at h
    · rename_i x0 y0 hl
      obtain ⟨hx, hc, he⟩ := liftX?_spec hl
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hx, ?_, ?_⟩
      · split
        · show _ * _ = _; rw [neg_sq]; exact hc
        · exact hc
      · by_cases hz : y0.toNat = 0
        · left
          split
          · rw [Fq.toF_neg]; have : y0.toF = 0 := Fin.ext hz
            rw [this]; decide
          · exact Fin.ext hz
        · right
          split
          · rename_i h3
            refine ⟨fun _ => h3, fun _ => ?_⟩
            have e := Fq.neg_toNat_of_pos (Nat.pos_of_ne_zero hz)
            have hlt : y0.toNat < P := y0.toF.isLt
            have := P_odd
            have he' : ¬ y0.toNat % 2 = 1 := by rw [← Fq.isOdd_iff, he]; simp
            rw [Fq.isOdd_iff, e]; omega
          · rename_i h3
            exact ⟨fun ho => (by rw [he] at ho; cases ho), fun e => absurd e h3⟩
    · cases h
  · cases h

/-! ## Tweaks -/

theorem tweak_spec {tb : ByteArray} {t : Nat} (h : tweak tb = .ok t) : tb.size = 32 ∧ t = fromBE tb ∧ t < N := by
  unfold tweak scalar? at h
  split at h
  · rename_i hs
    split at hs
    · rename_i hc; simp only [Option.some.injEq] at hs; cases h; exact ⟨hc.1, hs.symm, hs ▸ hc.2⟩
    · cases hs
  · cases h

/-- `PublicKey.adding`: the result is `t·G + K` on the spec curve. -/
theorem pointAdd_spec [FieldP] {x y x' y' : Fq} {tb : ByteArray} (h : pointAdd x y tb = .ok (x', y')) :
    ∃ t, tweak tb = .ok t ∧ Spec.Point.pt x'.toF y'.toF = Spec.add (Spec.smul t Spec.G) (.pt x.toF y.toF) := by
  unfold pointAdd at h
  cases ht : tweak tb with
  | error e => simp [ht, bind, Except.bind] at h
  | ok t =>
    refine ⟨t, rfl, ?_⟩
    simp only [ht, bind, Except.bind] at h
    cases hm : mulGAdd t (.pt x y) with
    | error e => simp [hm] at h
    | ok q =>
      simp only [hm] at h
      cases q with
      | inf => cases h
      | pt a b =>
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact mulGAdd_spec hm

/-- `XOnlyKey.adding`: the result is `t·G + lift_x(x)` (the even lift) on the spec curve. -/
theorem xonlyAdd_spec [FieldP] {x y x' y' : Fq} {tb : ByteArray} (h : xonlyAdd x y tb = .ok (x', y')) :
    ∃ t, tweak tb = .ok t ∧ Spec.Point.pt x'.toF y'.toF
      = Spec.add (Spec.smul t Spec.G) (.pt x.toF (if y.isOdd then -y else y).toF) := by
  unfold xonlyAdd at h
  cases ht : tweak tb with
  | error e => simp [ht, bind, Except.bind] at h
  | ok t =>
    refine ⟨t, rfl, ?_⟩
    simp only [ht, bind, Except.bind] at h
    cases hm : mulGAdd t (.pt x (if y.isOdd then -y else y)) with
    | error e => simp [hm] at h
    | ok q =>
      simp only [hm] at h
      cases q with
      | inf => cases h
      | pt a b =>
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact mulGAdd_spec hm

/-! ## BIP340 -/

theorem negPt_toSpec (p : APoint) : (negPt p).toSpec = Spec.neg p.toSpec := by
  cases p <;> simp [negPt, APoint.toSpec, Spec.neg, Fq.toF_neg]

/-- **Verification is BIP340's equation on the spec curve.** When `verify` accepts, the key is the
even lift of its x, `r < P`, `s < N`, and `s·G - e·P` is a finite point with an even y whose x is
`r`, for `e` the BIP340 challenge. -/
theorem verify_sound [FieldP] {sig m xb : ByteArray} (h : verify sig m xb = .ok true) :
    sig.size = 64 ∧ xb.size = 32 ∧
    ∃ px py, liftX? (fromBE xb) = some (px, py) ∧
      fromBE (sig.extract 0 32) < P ∧ fromBE (sig.extract 32 64) < N ∧
      ∃ rx ry : Spec.F,
        Spec.add (Spec.smul (fromBE (sig.extract 32 64)) Spec.G)
          (Spec.neg (Spec.smul (challenge (toBE32 (fromBE (sig.extract 0 32))) (toBE32 px.toNat) m)
                       (.pt px.toF py.toF))) = .pt rx ry
        ∧ rx.val = fromBE (sig.extract 0 32) ∧ ry.val % 2 = 0 := by
  unfold verify at h
  split at h
  · cases h
  · rename_i hsz
    have hsz' : sig.size = 64 := by simpa using hsz
    split at h
    · cases h
    · rename_i px py hl
      split at hl
      · rename_i hxb
        refine ⟨hsz', hxb, px, py, hl, ?_⟩
        simp only at h
        split at h
        · cases h
        · rename_i hrs
          simp only [not_or, Nat.not_le] at hrs
          refine ⟨hrs.1, hrs.2, ?_⟩
          split at h
          · cases h
          · rename_i eP heP
            split at h
            · cases h
            · cases h
            · rename_i x y hq
              simp only [Except.ok.injEq, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                beq_iff_eq] at h
              refine ⟨x.toF, y.toF, ?_, ?_, ?_⟩
              · have := mulGAdd_spec hq
                rw [negPt_toSpec, mulPt_spec heP] at this
                exact this.symm
              · exact h.2
              · have := h.1; rw [Fq.isOdd] at this; simp only [beq_eq_false_iff_ne] at this
                show y.toNat % 2 = 0; omega
      · cases hl

/-- `PrivateKey.adding`: `(d + t) mod N`, never zero. -/
theorem secretAdd_spec {d s : Nat} {tb : ByteArray} (h : secretAdd d tb = .ok s) :
    ∃ t, tweak tb = .ok t ∧ s = (d + t) % N ∧ s ≠ 0 := by
  unfold secretAdd at h
  cases ht : tweak tb with
  | error e => rw [ht] at h; cases h
  | ok t =>
    rw [ht] at h
    dsimp only at h
    by_cases hz : (d + t) % N = 0
    · simp [hz] at h
    · simp only [hz, ite_false, Except.ok.injEq] at h
      exact ⟨t, rfl, h.symm, h ▸ hz⟩

/-- `PrivateKey.addingXOnly`: `d` is negated exactly when `d·G` (on the spec curve) has an odd y. -/
theorem secretAddXOnly_spec [FieldP] {d s : Nat} {tb : ByteArray} (h : secretAddXOnly d tb = .ok s) :
    ∃ t px py, pubOf d = .ok (px, py) ∧ Spec.smul d Spec.G = .pt px.toF py.toF ∧ tweak tb = .ok t
      ∧ s = ((if py.isOdd then negN d else d) + t) % N ∧ s ≠ 0 := by
  unfold secretAddXOnly at h
  cases hp : pubOf d with
  | error e => rw [hp] at h; cases h
  | ok q =>
    obtain ⟨px, py⟩ := q
    rw [hp] at h
    cases ht : tweak tb with
    | error e => simp only [ht] at h; cases h
    | ok t =>
      simp only [ht] at h
      by_cases hz : ((if py.isOdd then negN d else d) + t) % N = 0
      · simp [hz] at h
      · simp only [hz, ite_false, Except.ok.injEq] at h
        exact ⟨t, px, py, rfl, pubOf_spec hp, rfl, h.symm, h ▸ hz⟩

/-- The key `signRaw` signs under is the signer's own x-only key. -/
theorem signRaw_key {m aux : ByteArray} {d : Nat} {r : ByteArray × ByteArray} (h : signRaw m d aux = .ok r) :
    ∃ px py, pubOf d = .ok (px, py) ∧ r.2 = toBE32 px.toNat := by
  unfold signRaw at h
  by_cases ha : aux.size ≠ 32
  · simp [ha] at h
  · simp only [ha, ite_false] at h
    cases hp : pubOf d with
    | error e => rw [hp] at h; cases h
    | ok q =>
      obtain ⟨px, py⟩ := q
      refine ⟨px, py, rfl, ?_⟩
      rw [hp] at h
      simp only at h
      generalize hk : hashMod _ = k0 at h
      by_cases hz : k0 = 0
      · simp [hz] at h
      · simp only [hz, ite_false] at h
        cases hg : mulG k0 with
        | error e => rw [hg] at h; cases h
        | ok q =>
          rw [hg] at h
          cases q with
          | inf => cases h
          | pt x y => cases h; rfl

/-- **A signature the oracle returns verifies under the signer's x-only key** (the x of `d·G`),
so by `verify_sound` it satisfies BIP340's equation on the spec curve. -/
theorem sign_verifies {m aux sig : ByteArray} {d : Nat} (h : sign m d aux = .ok sig) :
    ∃ px py, pubOf d = .ok (px, py) ∧ verify sig m (toBE32 px.toNat) = .ok true := by
  unfold sign at h
  split at h
  · cases h
  · rename_i sig' pxb hr
    obtain ⟨px, py, hp, hk⟩ := signRaw_key hr
    simp only at hk
    split at h
    · rename_i hv; cases h; exact ⟨px, py, hp, hk ▸ hv⟩
    · cases h
    · cases h

end Secp
