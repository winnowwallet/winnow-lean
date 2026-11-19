import SecpCt.EcdsaProofs
import SecpCt.Keys

/-! # What the public-key functions are, on the curve as specified

`SecpCt/Keys.lean` reads public keys, tweaks them and checks signatures. Here each of those is said in the
specification's terms (`Secp/Curve/Spec.lean`):

  - a key that is read is a point of the curve with the coordinates its bytes spell (`parseXOnly_spec`,
    `parseCompressed_spec`, `parseUncompressed_spec`, `liftX?_spec`), with no assumption about P;
  - the tweaks are the specification's sums and products (`pointAdd_spec`, `pointMul_spec`,
    `generatorMul_spec`, `combine_spec`, `publicPoint_spec`, `evenKey_spec`);
  - a signature that is accepted satisfies its scheme's equation (`verify_sound`, `Ecdsa.verify_sound`),
    and a signature `signVerified` returns is one `verify` accepts (`signVerified_verifies`).

The statements about sums and products assume P is prime, as Fermat's little theorem for P (`[Fermat]`,
`SecpCt/CurveProofs.lean`): two coordinates are had from three by a division, which here is a power. It is a
hypothesis, never an axiom.

Nothing that runs imports this file; `SecpCt/Gate.lean` does. -/

namespace SecpCt
open Secp.Spec (F OnCurve)
open Secp

/-! ## Elements read and compared -/

/-- Two elements `same` says are the same are the same. -/
theorem Fe.same_eq {a b : Fe} (h : Fe.same a b = true) : a = b := by
  cases a; cases b
  simp only [Fe.same, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  subst h0 h1 h2 h3
  rfl

theorem Sc.same_eq {a b : Sc} (h : Sc.same a b = true) : a = b := by
  cases a; cases b
  simp only [Sc.same, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  subst h0 h1 h2 h3
  rfl

/-- A power is below P. -/
theorem power_valid (a : Fe) (e0 e1 e2 e3 : UInt64) : (Fe.power a e0 e1 e2 e3).Valid := by
  rw [Fe.Valid, power_spec]
  exact Nat.mod_lt _ (by decide)

/-- An element whose square is `same` as another squares to it. -/
theorem squares_of_same {a r : Fe} (h : Fe.same (Fe.sqr r) a = true) : r.toF * r.toF = a.toF := by
  rw [← toF_mul, ← Fe.same_eq h, Fe.sqr]

/-- What `sqrt?` returns squares to what it was given: the answer is checked, so this needs nothing about P. -/
theorem sqrt?_sound {a r : Fe} (h : Fe.sqrt? a = some r) : r.toF * r.toF = a.toF ∧ r.Valid := by
  unfold Fe.sqrt? at h
  generalize root : Fe.power a _ _ _ _ = candidate at h
  have valid : candidate.Valid := root ▸ power_valid a _ _ _ _
  by_cases squares : Fe.same (Fe.sqr candidate) a = true
  · simp only [squares, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨squares_of_same squares, valid⟩
  · simp only [squares, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- 32 bytes that `ofBytes?` takes spell a number below P, and it is that number. -/
theorem Fe.ofBytes?_spec {b : ByteArray} {x : Fe} (h : Fe.ofBytes? b = some x) :
    b.size = 32 ∧ x.toNat = Secp.fromBE b ∧ x.Valid := by
  simp only [Fe.ofBytes?] at h
  split at h
  · cases h
  · rename_i size
    have size : b.size = 32 := by simpa using size
    split at h
    · rename_i unchanged
      cases h
      have reduced := Fe.ofBytes_spec b size
      have valid : (Fe.ofBytes b).Valid := canon_lt _ _ _ _
      refine ⟨size, ?_, valid⟩
      -- the words as they stand are the number the bytes spell
      have words : (Fe.ofBytes b).toNat = Secp.fromBE b := by
        obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
          b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32 b size
        rw [Fe.same_eq unchanged, fromBE_words]
        rfl
      exact words
    · cases h

theorem seven_toNat : seven.toNat = 7 := by
  simp only [seven, Fe.ofWord, Fe.toNat, value, show (0 : UInt64).toNat = 0 from rfl, show (7 : UInt64).toNat = 7 from rfl]

theorem seven_valid : seven.Valid := by
  rw [Fe.Valid, seven_toNat]
  decide

theorem seven_toF : seven.toF = 7 := by
  rw [Fe.toF, seven_toNat]
  rfl

/-- The right-hand side of the curve's equation, as the code computes it. -/
theorem cubic_toF (x : Fe) : (Fe.add (Fe.mul (Fe.sqr x) x) seven).toF = x.toF * x.toF * x.toF + 7 := by
  rw [toF_add _ _ (valid_mul _ _) seven_valid, toF_mul, Fe.sqr, toF_mul, seven_toF]

theorem P_odd : P % 2 = 1 := by decide

/-- The arithmetic of the other y: an odd number below an odd modulus, taken from it, is even. -/
theorem odd_complement (p y : Nat) (oddP : p % 2 = 1) (below : y < p) (odd : y % 2 = 1) : (p - y) % p % 2 = 0 := by
  have small : p - y < p := by omega
  rw [Nat.mod_eq_of_lt small]
  omega

/-- An odd element below P, taken from P, is even: P is odd. -/
theorem neg_even (y : Fe) (valid : y.Valid) (odd : y.toNat % 2 = 1) : (Fe.neg y).toNat % 2 = 0 := by
  rw [neg_spec y valid]
  exact odd_complement P y.toNat P_odd valid odd

/-- **`lift_x`.** The point `liftX?` gives has the x it was given, is on the curve, and has an even y. -/
theorem liftX?_spec {x : Fe} {p : Affine} (h : liftX? x = some p) :
    p.x = x ∧ p.y.toF * p.y.toF = x.toF * x.toF * x.toF + 7 ∧ p.y.Valid ∧ p.y.toNat % 2 = 0 := by
  unfold liftX? at h
  -- the root is named, never looked into: taking the power apart would be 255 squarings written out
  obtain ⟨y, root, made⟩ := Option.map_eq_some_iff.mp h
  subst made
  obtain ⟨squares, valid⟩ := sqrt?_sound root
  rw [cubic_toF] at squares
  have parity := Fe.isOdd_spec y
  by_cases odd : y.isOdd = 1
  · have isOdd : y.toNat % 2 = 1 := by rw [← parity, odd]; rfl
    simp only [odd, beq_self_eq_true, ↓reduceIte]
    refine ⟨trivial, ?_, valid_neg _ valid, neg_even y valid isOdd⟩
    rw [toF_neg _ valid, ← squares]
    grind
  · have even : y.toNat % 2 = 0 := by
      have two : y.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
      have notOne : y.toNat % 2 ≠ 1 := fun e => odd (UInt64.toNat_inj.mp (by rw [parity, e]; rfl))
      omega
    have unset : (y.isOdd == 1) = false := by simpa using odd
    simp only [unset, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, squares, valid, even⟩

/-- A point of the curve as the specification has it. -/
def Affine.spec (p : Affine) : Spec.Point := .pt p.x.toF p.y.toF

/-- What every `Affine` this library makes is: two coordinates below P that are a point of the curve. -/
def Affine.Good (p : Affine) : Prop := p.x.Valid ∧ p.y.Valid ∧ OnCurve p.spec

/-- **A BIP 340 public key.** 32 bytes `parseXOnly` takes spell an x below P; the point is on the curve, has
that x and an even y. -/
theorem parseXOnly_spec {b : ByteArray} {p : Affine} (h : parseXOnly b = some p) :
    b.size = 32 ∧ p.x.toNat = Secp.fromBE b ∧ p.Good ∧ p.y.toNat % 2 = 0 := by
  unfold parseXOnly at h
  obtain ⟨x, read, lifted⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨size, number, valid⟩ := Fe.ofBytes?_spec read
  obtain ⟨same, curve, yValid, even⟩ := liftX?_spec lifted
  refine ⟨size, by rw [same, number], ⟨by rw [same]; exact valid, yValid, ?_⟩, even⟩
  show p.y.toF * p.y.toF = p.x.toF * p.x.toF * p.x.toF + 7
  rw [same]
  exact curve

theorem Affine.neg_good {p : Affine} (h : p.Good) : p.neg.Good := by
  obtain ⟨vx, vy, curve⟩ := h
  refine ⟨vx, valid_neg _ vy, ?_⟩
  show (Fe.neg p.y).toF * (Fe.neg p.y).toF = p.x.toF * p.x.toF * p.x.toF + 7
  have curve : p.y.toF * p.y.toF = p.x.toF * p.x.toF * p.x.toF + 7 := curve
  rw [toF_neg _ vy, ← curve]
  grind

/-- **A compressed public key.** 33 bytes `parseCompressed` takes are 02 or 03 and an x below P; the point is
on the curve and has that x. -/
theorem parseCompressed_spec {b : ByteArray} {p : Affine} (h : parseCompressed b = some p) :
    b.size = 33 ∧ p.x.toNat = Secp.fromBE (b.extract 1 33) ∧ p.Good := by
  unfold parseCompressed at h
  split at h
  · rename_i size
    dsimp only at h
    split at h
    · obtain ⟨q, parsed, made⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨_, number, good, _⟩ := parseXOnly_spec parsed
      subst made
      split
      · exact ⟨size, number, Affine.neg_good good⟩
      · exact ⟨size, number, good⟩
    · cases h
  · cases h

/-- Whether the curve's equation holds, as `onCurve` checks it, is whether it holds. -/
theorem onCurve_spec {x y : Fe} (h : onCurve x y = true) : y.toF * y.toF = x.toF * x.toF * x.toF + 7 := by
  have equal := Fe.same_eq h
  rw [← cubic_toF, ← equal, Fe.sqr, toF_mul]

/-- **An uncompressed public key.** 65 bytes `parseUncompressed` takes are an x and a y below P that are a
point of the curve. -/
theorem parseUncompressed_spec {b : ByteArray} {p : Affine} (h : parseUncompressed b = some p) :
    b.size = 65 ∧ p.x.toNat = Secp.fromBE (b.extract 1 33) ∧ p.y.toNat = Secp.fromBE (b.extract 33 65) ∧ p.Good := by
  unfold parseUncompressed at h
  split at h
  · rename_i size
    dsimp only at h
    split at h
    · obtain ⟨x, readX, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, readY, made⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨_, numberX, validX⟩ := Fe.ofBytes?_spec readX
      obtain ⟨_, numberY, validY⟩ := Fe.ofBytes?_spec readY
      split at made
      · rename_i fits
        injection made with made
        subst made
        simp only [Bool.and_eq_true] at fits
        exact ⟨size, numberX, numberY, validX, validY, onCurve_spec fits.1⟩
      · cases made
    · cases h
  · cases h

/-! ## Numbers that are not secret -/

/-- `isBelowN` says whether thirty-two bytes spell a number below N. -/
theorem Sc.isBelowN_spec (b : ByteArray) (h : b.size = 32) :
    Sc.isBelowN b = if Secp.fromBE b < N then 1 else 0 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
    b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32 b h
  rw [fromBE_words]
  simp only [Sc.isBelowN]
  generalize wordAt _ 24 = u0
  generalize wordAt _ 16 = u1
  generalize wordAt _ 8 = u2
  generalize wordAt _ 0 = u3
  have below := lessN_below u0 u1 u2 u3
  apply UInt64.toNat_inj.mp
  rw [below]
  split <;> rfl

/-- A number `scalar?` takes is the number its 32 bytes spell, and is below N. -/
theorem scalar?_spec {b : ByteArray} {t : Sc} (h : scalar? b = some t) :
    b.size = 32 ∧ t.toNat = Secp.fromBE b ∧ Secp.fromBE b < N := by
  unfold scalar? at h
  rcases Bool.eq_false_or_eq_true (b.size == 32 && Sc.isBelowN b == 1) with fits | fits
  · simp only [fits, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    obtain ⟨size, flag⟩ := fits
    have below : Secp.fromBE b < N := by
      rw [Sc.isBelowN_spec b size] at flag
      by_cases lt : Secp.fromBE b < N
      · exact lt
      · simp only [lt, ↓reduceIte] at flag
        exact absurd flag (by decide)
    exact ⟨size, by rw [Sc.ofBytes_spec b size, Nat.mod_eq_of_lt below], below⟩
  · simp only [fits, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-! ## Back from three coordinates to two -/

theorem neg_onCurve {p : Spec.Point} (h : OnCurve p) : OnCurve (Spec.neg p) :=
  Spec.neg_onCurve h

/-- A point of this library stands, in three coordinates, for the point it names. -/
theorem Affine.rep {p : Affine} (good : p.Good) : Rep p.point p.spec := rep_ofAffine good.1 good.2.1

/-- **Reading a result off.** When `toAffine?` gives two coordinates for a point that stands for a point of
the curve, they name that point. -/
theorem toAffine?_spec {p : Point} {c : Spec.Point} (curve : OnCurve c) (rep : Rep p c) {q : Affine}
    (made : p.toAffine? = some q) : c = q.spec ∧ q.Good := by
  unfold Point.toAffine? at made
  have spec := affine_spec rep
  -- the coordinates are named, never looked into: the division behind them is a power written out
  generalize p.affine = t at made spec
  rcases Bool.eq_false_or_eq_true (t.2.2 == 1) with flag | flag
  · simp only [flag, ↓reduceIte, reduceCtorEq] at made
  · simp only [flag, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at made
    subst made
    rcases spec with ⟨one, _⟩ | ⟨_, point, vx, vy⟩
    · rw [one] at flag
      exact absurd flag (by decide)
    · refine ⟨point, vx, vy, ?_⟩
      rw [point] at curve
      exact curve

/-- And when it gives none, the point stands for the point at infinity. -/
theorem toAffine?_none {p : Point} {c : Spec.Point} (rep : Rep p c) (made : p.toAffine? = none) :
    c = .inf := by
  unfold Point.toAffine? at made
  have spec := affine_spec rep
  generalize p.affine = t at made spec
  rcases Bool.eq_false_or_eq_true (t.2.2 == 1) with flag | flag
  · rcases spec with ⟨_, inf⟩ | ⟨zero, _⟩
    · exact inf
    · rw [zero] at flag
      exact absurd flag (by decide)
  · simp only [flag, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at made

/-! ## Sums and products -/

/-- **`t·G`.** -/
theorem generatorMul_spec {t : Sc} {q : Affine} (h : generatorMul t = some q) :
    Spec.smul t.toNat Spec.G = q.spec ∧ q.Good :=
  toAffine?_spec (Spec.smul_onCurve _ Spec.G_onCurve) (mulPublic_rep t Spec.G_onCurve rep_generator) h

/-- **A secret's public point** is `d·G`. -/
theorem publicPoint_spec {d : Sc} {q : Affine} (h : publicPoint d = some q) :
    Spec.smul d.toNat Spec.G = q.spec ∧ q.Good :=
  toAffine?_spec (Spec.smul_onCurve _ Spec.G_onCurve) (mulGenerator_rep d) h

/-- **`t·G + P`**: the tweak of BIP 32's public derivation and of BIP 341's output key. -/
theorem pointAdd_spec {p q : Affine} {t : Sc} (good : p.Good) (h : pointAdd p t = some q) :
    Spec.add (Spec.smul t.toNat Spec.G) p.spec = q.spec ∧ q.Good :=
  toAffine?_spec (Spec.add_onCurve (Spec.smul_onCurve _ Spec.G_onCurve) good.2.2)
    (rep_add (Spec.smul_onCurve _ Spec.G_onCurve) good.2.2 (mulPublic_rep t Spec.G_onCurve rep_generator)
      (Affine.rep good)) h

/-- **`k·P`**, for any point of the curve this library has read. -/
theorem pointMul_spec {p q : Affine} {k : Sc} (good : p.Good) (h : pointMul k p = some q) :
    Spec.smul k.toNat p.spec = q.spec ∧ q.Good :=
  toAffine?_spec (Spec.smul_onCurve _ good.2.2) (mul_rep k good.2.2 (Affine.rep good)) h

theorem sum_rep (points : List Affine) (good : ∀ p ∈ points, p.Good) (acc : Point) (c : Spec.Point)
    (curve : OnCurve c) (rep : Rep acc c) :
    OnCurve (points.foldl (fun sum p => Spec.add sum p.spec) c) ∧
    Rep (points.foldl (fun sum p => Point.add sum p.point) acc)
      (points.foldl (fun sum p => Spec.add sum p.spec) c) := by
  induction points generalizing acc c with
  | nil => exact ⟨curve, rep⟩
  | cons p rest ih =>
    have here := good p List.mem_cons_self
    exact ih (fun r member => good r (List.mem_cons_of_mem _ member)) _ _ (Spec.add_onCurve curve here.2.2)
      (rep_add curve here.2.2 rep (Affine.rep here))

/-- **A sum of points**, added in the order given, starting from the point at infinity. -/
theorem combine_spec {points : List Affine} {q : Affine} (good : ∀ p ∈ points, p.Good)
    (h : combine points = some q) :
    points.foldl (fun sum p => Spec.add sum p.spec) .inf = q.spec ∧ q.Good :=
  have ⟨curve, rep⟩ := sum_rep points good Point.infinity .inf trivial rep_infinity
  toAffine?_spec curve rep h

/-- **The key with the even y.** For a secret `d` below N whose public point is `(x, y)`, `evenKey d` is `d`
if `y` is even and `N − d` if it is odd. -/
theorem evenKey_spec (d : Sc) (below : d.toNat < N) {x y : F}
    (point : Spec.smul d.toNat Spec.G = .pt x y) :
    (evenKey d).toNat = if y.val % 2 = 1 then (N - d.toNat) % N else d.toNat := by
  unfold evenKey
  have spec := affine_spec (mulGenerator_rep d)
  rw [point] at spec
  generalize (Point.mulGenerator d).affine = t at spec
  rcases spec with ⟨_, inf⟩ | ⟨_, same, _, vy⟩
  · cases inf
  · injection same with _ sameY
    have number : t.2.1.toNat = y.val := Fe.toNat_of_toF vy sameY.symm
    have parity := Fe.isOdd_spec t.2.1
    rw [number] at parity
    by_cases odd : y.val % 2 = 1
    · have flag : t.2.1.isOdd = 1 := UInt64.toNat_inj.mp (by rw [parity, odd]; rfl)
      rw [flag, Sc.negIf_one, Sc.neg_spec _ below]
      simp only [odd, ↓reduceIte]
    · have even : y.val % 2 = 0 := by
        have two : y.val % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      have flag : t.2.1.isOdd = 0 := UInt64.toNat_inj.mp (by rw [parity, even]; rfl)
      rw [flag, Sc.negIf_zero]
      simp only [odd, ↓reduceIte]

/-! ## Signatures -/

theorem extract_size (b : ByteArray) (from' to : Nat) (h : to ≤ b.size) : (b.extract from' to).size = to - from' := by
  rw [ByteArray.size_extract]
  omega

/-- **Verification is BIP 340's equation on the curve as specified.** When `verify` accepts, the key's 32
bytes spell the x of a point of the curve, taken with its even y; `r` is below P and `s` below N; and
`s·G − e·P` is a point, not the point at infinity, with an even y, whose x is `r`: for `e` the BIP 340
challenge. -/
theorem verify_sound {signature message key : ByteArray} (h : verify signature message key = true) :
    signature.size = 64 ∧ key.size = 32 ∧
    Secp.fromBE (signature.extract 0 32) < P ∧ Secp.fromBE (signature.extract 32 64) < N ∧
    ∃ px py : F, px.val = Secp.fromBE key ∧ py * py = px * px * px + 7 ∧ py.val % 2 = 0 ∧
      ∃ rx ry : F,
        Spec.add (Spec.smul (Secp.fromBE (signature.extract 32 64)) Spec.G)
          (Spec.neg (Spec.smul
            (Secp.challenge (Secp.toBE32 (Secp.fromBE (signature.extract 0 32))) (Secp.toBE32 px.val) message)
            (.pt px py))) = .pt rx ry
        ∧ rx.val = Secp.fromBE (signature.extract 0 32) ∧ ry.val % 2 = 0 := by
  unfold verify at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨size, sum, found⟩ := h
  obtain ⟨p, parsed, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨r, readR, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨s, readS, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨made, checks⟩ := Option.filter_eq_some_iff.mp found
  obtain ⟨keySize, keyNumber, good, keyEven⟩ := parseXOnly_spec parsed
  obtain ⟨_, rNumber, rValid⟩ := Fe.ofBytes?_spec readR
  obtain ⟨_, sNumber, sBelow⟩ := scalar?_spec readS
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at checks
  obtain ⟨sumEven, sameX⟩ := checks
  have sameX := Fe.same_eq sameX
  -- the sum the verifier formed stands for the specification's
  have curveP : OnCurve (Spec.smul
      (Sc.ofBytes (Secp.Sha256.tagged "BIP0340/challenge" (r.bytes ++ p.x.bytes ++ message))).toNat p.spec) :=
    Spec.smul_onCurve _ good.2.2
  obtain ⟨equation, sumGood⟩ := toAffine?_spec
    (Spec.add_onCurve (Spec.smul_onCurve _ Spec.G_onCurve) (neg_onCurve curveP))
    (rep_add (Spec.smul_onCurve _ Spec.G_onCurve) (neg_onCurve curveP)
      (mulPublic_rep s Spec.G_onCurve rep_generator) (rep_neg (mulPublic_rep _ good.2.2 (Affine.rep good)))) made
  have pxVal : p.x.toF.val = p.x.toNat := by rw [Fe.toF_val, Nat.mod_eq_of_lt good.1]
  have pyVal : p.y.toF.val = p.y.toNat := by rw [Fe.toF_val, Nat.mod_eq_of_lt good.2.1]
  have sxVal : sum.x.toF.val = sum.x.toNat := by rw [Fe.toF_val, Nat.mod_eq_of_lt sumGood.1]
  have syVal : sum.y.toF.val = sum.y.toNat := by rw [Fe.toF_val, Nat.mod_eq_of_lt sumGood.2.1]
  have challenge : (Sc.ofBytes (Secp.Sha256.tagged "BIP0340/challenge" (r.bytes ++ p.x.bytes ++ message))).toNat
      = Secp.challenge (Secp.toBE32 (Secp.fromBE (signature.extract 0 32))) (Secp.toBE32 p.x.toF.val) message := by
    rw [Sc.ofBytes_spec _ (tagged_size _ _), Fe.bytes_spec, Fe.bytes_spec, rNumber, pxVal, N_eq]
    rfl
  have rBelow : Secp.fromBE (signature.extract 0 32) < P := by rw [← rNumber]; exact rValid
  refine ⟨size, keySize, rBelow, sBelow, p.x.toF, p.y.toF, by rw [pxVal, keyNumber], good.2.2,
    by rw [pyVal]; exact keyEven, sum.x.toF, sum.y.toF, ?_, by rw [sxVal, sameX, rNumber], ?_⟩
  · rw [← sNumber, ← challenge]
    exact equation
  · rw [syVal]
    have parity := Fe.isOdd_spec sum.y
    have notOdd : sum.y.isOdd ≠ 1 := by
      intro odd
      simp only [Affine.isOdd, odd, beq_self_eq_true, Bool.true_eq_false] at sumEven
    have two : sum.y.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    have notOne : sum.y.toNat % 2 ≠ 1 := fun e => notOdd (UInt64.toNat_inj.mp (by rw [parity, e]; rfl))
    omega

/-- **A signature `signVerified` returns is one `verify` accepts** under the signer's own public key, and is
the one `sign` made. -/
theorem signVerified_verifies {secret message aux signature : ByteArray}
    (h : signVerified secret message aux = some signature) :
    sign secret message aux = some signature ∧
    ∃ key, publicKey secret = some key ∧ verify signature message key.1 = true := by
  unfold signVerified at h
  obtain ⟨made, checked⟩ := Option.filter_eq_some_iff.mp h
  exact ⟨made, (Option.any_eq_true _ _).mp checked⟩

/-- **Verification is ECDSA's equation on the curve as specified.** When `Ecdsa.verify` accepts, the
signature is 64 bytes spelling `r` and `s` with `0 < r < N` and `0 < s ≤ N/2`, the key is a point of the
curve that `parseCompressed` read, and there is a `w` with `s·w = 1` modulo N for which `(z·w)·G + (r·w)·Q`
is a point, not the point at infinity, whose x modulo N is `r`: for `z` the digest as a number modulo N and
`Q` the key. Nothing here rests on N being prime. -/
theorem Ecdsa.verify_sound {signature digest key : ByteArray}
    (h : Ecdsa.verify signature digest key = true) :
    signature.size = 64 ∧ digest.size = 32 ∧
    0 < Secp.fromBE (signature.extract 0 32) ∧ Secp.fromBE (signature.extract 0 32) < N ∧
    0 < Secp.fromBE (signature.extract 32 64) ∧ Secp.fromBE (signature.extract 32 64) ≤ N / 2 ∧
    ∃ q : Affine, parseCompressed key = some q ∧ q.Good ∧
      ∃ w, Secp.fromBE (signature.extract 32 64) * w % N = 1 ∧
        ∃ x y : F,
          Spec.add (Spec.smul (Secp.fromBE digest % N * w % N) Spec.G)
            (Spec.smul (Secp.fromBE (signature.extract 0 32) * w % N) q.spec) = .pt x y
          ∧ x.val % N = Secp.fromBE (signature.extract 0 32) := by
  unfold Ecdsa.verify at h
  dsimp only at h
  -- the division is named, never looked into
  generalize Sc.inv (Sc.ofBytes (signature.extract 32 64)) = w at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨⟨⟨size, digestSize⟩, keyR⟩, keyS⟩, low⟩, inverse⟩, sum, found⟩ := h
  obtain ⟨q, parsed, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨made, sameR⟩ := Option.filter_eq_some_iff.mp found
  obtain ⟨_, _, good⟩ := parseCompressed_spec parsed
  have rSize : (signature.extract 0 32).size = 32 := extract_size _ _ _ (by omega)
  have sSize : (signature.extract 32 64).size = 32 := extract_size _ _ _ (by omega)
  rw [Sc.isKey_spec _ rSize] at keyR
  rw [Sc.isKey_spec _ sSize] at keyS
  have rRange : 0 < Secp.fromBE (signature.extract 0 32) ∧ Secp.fromBE (signature.extract 0 32) < N := by
    by_cases range : 0 < Secp.fromBE (signature.extract 0 32) ∧ Secp.fromBE (signature.extract 0 32) < N
    · exact range
    · simp only [range, ↓reduceIte] at keyR
      exact absurd keyR (by decide)
  have sRange : 0 < Secp.fromBE (signature.extract 32 64) ∧ Secp.fromBE (signature.extract 32 64) < N := by
    by_cases range : 0 < Secp.fromBE (signature.extract 32 64) ∧ Secp.fromBE (signature.extract 32 64) < N
    · exact range
    · simp only [range, ↓reduceIte] at keyS
      exact absurd keyS (by decide)
  have rNumber : (Sc.ofBytes (signature.extract 0 32)).toNat = Secp.fromBE (signature.extract 0 32) := by
    rw [Sc.ofBytes_spec _ rSize]
    exact Nat.mod_eq_of_lt rRange.2
  have sNumber : (Sc.ofBytes (signature.extract 32 64)).toNat = Secp.fromBE (signature.extract 32 64) := by
    rw [Sc.ofBytes_spec _ sSize]
    exact Nat.mod_eq_of_lt sRange.2
  have sLow : Secp.fromBE (signature.extract 32 64) ≤ N / 2 := by
    rw [Sc.isHigh_spec, sNumber] at low
    by_cases high : Secp.fromBE (signature.extract 32 64) > N / 2
    · simp only [high, ↓reduceIte] at low
      exact absurd low (by decide)
    · omega
  have divides : Secp.fromBE (signature.extract 32 64) * w.toNat % N = 1 := by
    have product := congrArg Sc.toNat (Sc.same_eq inverse)
    rw [Sc.mul_spec, Sc.one_toNat, sNumber] at product
    exact product
  obtain ⟨equation, sumGood⟩ := toAffine?_spec
    (Spec.add_onCurve (Spec.smul_onCurve _ Spec.G_onCurve) (Spec.smul_onCurve _ good.2.2))
    (rep_add (Spec.smul_onCurve _ Spec.G_onCurve) (Spec.smul_onCurve _ good.2.2)
      (mulPublic_rep _ Spec.G_onCurve rep_generator) (mulPublic_rep _ good.2.2 (Affine.rep good))) made
  rw [Sc.mul_spec, Sc.mul_spec, Sc.ofBytes_spec _ digestSize, rNumber] at equation
  refine ⟨size, digestSize, rRange.1, rRange.2, sRange.1, sLow, q, parsed, good, w.toNat, divides,
    sum.x.toF, sum.y.toF, equation, ?_⟩
  have reduced := congrArg Sc.toNat (Sc.same_eq sameR)
  rw [reduceOnce_mod, rNumber] at reduced
  rw [Fe.toF_val, Nat.mod_eq_of_lt sumGood.1]
  exact reduced

/-- **A signature `Ecdsa.signVerified` returns is one `Ecdsa.verify` accepts** under the signer's own public
key, compressed, and is the one `Ecdsa.sign` made. -/
theorem Ecdsa.signVerified_verifies {secret digest aux signature : ByteArray}
    (h : Ecdsa.signVerified secret digest aux = some signature) :
    Ecdsa.sign secret digest aux = some signature ∧
    ∃ key, publicPoint (Sc.ofBytes secret) = some key ∧ Ecdsa.verify signature digest key.compressed = true := by
  unfold Ecdsa.signVerified at h
  obtain ⟨made, checked⟩ := Option.filter_eq_some_iff.mp h
  exact ⟨made, (Option.any_eq_true _ _).mp checked⟩

end SecpCt
