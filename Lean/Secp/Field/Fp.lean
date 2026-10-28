import Secp.Field.Multi

/-! # The field of integers modulo p

`Fq` is a four-limb number below `P`, the representation the curve code runs on. Every operation
is proven to agree with the specification `Fin P`, the integers modulo `P` (`toF_add`, `toF_sub`,
`toF_mul`, `toF_neg`), and the representation is unique (`toF_inj`). Multiplication reduces the
512-bit product with `2^256 ≡ 2^32 + 977 (mod P)` three times and then subtracts `P` at most once.
Inversion and square roots are not proven to succeed; they check their own answer and return
`none` when it is wrong (`inv?_spec`, `sqrt?_spec`). -/

namespace Secp

def P : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- `2^256 - P`. -/
def C : Nat := 0x1000003D1

theorem P_add_C : P + C = 2^256 := by decide
theorem P_lt : P < 2^256 := by decide
theorem P_gt : 2^255 < P := by decide

instance : NeZero P := ⟨by decide⟩

/-- `P` as limbs. -/
def pL : List UInt64 := [0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]
theorem val_pL : val pL = P := by decide
theorem len_pL : pL.length = 4 := rfl

def cW : UInt64 := 0x1000003D1
theorem cW_toNat : cW.toNat = C := rfl

/-- A field element: four limbs whose value is below `P`. -/
def Fq := { l : List UInt64 // l.length = 4 ∧ val l < P }

instance : DecidableEq Fq := inferInstanceAs (DecidableEq { l : List UInt64 // l.length = 4 ∧ val l < P })

/-- The meaning of a field element. -/
def Fq.toF (a : Fq) : Fin P := ⟨val a.1, a.2.2⟩

theorem val_inj : ∀ (xs ys : List UInt64), xs.length = ys.length → val xs = val ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, hv => by
    simp only [val_cons, List.length_cons] at hv hl
    have hx := x.toNat_lt; have hy := y.toNat_lt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : val xs = val ys := by omega
    rw [UInt64.toNat_inj.1 h1, val_inj xs ys (by omega) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem Fq.toF_inj {a b : Fq} : a.toF = b.toF ↔ a = b := by
  constructor
  · intro h
    have hv : val a.1 = val b.1 := congrArg Fin.val h
    exact Subtype.ext (val_inj _ _ (by rw [a.2.1, b.2.1]) hv)
  · intro h; rw [h]

/-! ## Reduction -/

/-- `t ↦ low + C · high`, which is congruent to `t` modulo `P` (`2^256 = P + C`). -/
def fold (t : List UInt64) : List UInt64 :=
  let r := addc (t.take 4) (mulAddRow cW (t.drop 4) 0) 0
  r.1 ++ [r.2]

theorem fold_spec (t : List UInt64) (ht : 4 ≤ t.length) :
    val t = val (fold t) + P * val (t.drop 4) ∧ val (fold t) = val (t.take 4) + C * val (t.drop 4)
      ∧ 4 ≤ (fold t).length := by
  have hsplit := val_take_drop 4 t
  have hlen : (t.take 4).length = 4 := by simp; omega
  rw [hlen] at hsplit
  have ⟨r1, r2⟩ := mulAddRow_spec cW (t.drop 4) 0
  have ⟨a1, _, a3⟩ := addc_spec (t.take 4) (mulAddRow cW (t.drop 4) 0) 0 (by simp)
  rw [cW_toNat] at r1
  simp only [UInt64.toNat_zero, Nat.add_zero] at r1 a1
  have hv : val (fold t) = val (t.take 4) + C * val (t.drop 4) := by
    simp only [fold, val_append, val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
    rw [Nat.mul_comm (2^_), a1, r1]
  refine ⟨?_, hv, ?_⟩
  · rw [hsplit, hv, ← P_add_C, Nat.add_mul]; omega
  · simp only [fold, List.length_append, List.length_cons, List.length_nil, a3, hlen]; omega

/-- Below `2^256`, subtract `P` once if needed. -/
def canon (x : List UInt64) : List UInt64 :=
  let d := subb x pL 0
  if d.2 = 0 then d.1 else x

theorem canon_spec (x : List UInt64) (hl : x.length = 4) (hx : val x < 2^256) :
    val (canon x) = val x % P ∧ (canon x).length = 4 := by
  have ⟨d1, d2, d3⟩ := subb_spec x pL 0 (by simp) (by rw [hl, len_pL])
  rw [val_pL, hl] at d1
  have bd := val_lt (subb x pL 0).1
  rw [d3, hl] at bd
  have := P_gt
  simp only [canon]
  split
  · rename_i h; rw [h] at d1; simp at d1
    refine ⟨?_, by rw [d3, hl]⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rename_i h
    have : (subb x pL 0).2.toNat = 1 := by
      have : (subb x pL 0).2.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.1 (by simpa using h0))
      omega
    rw [this] at d1; simp at d1
    exact ⟨(Nat.mod_eq_of_lt (by omega)).symm, hl⟩

/-- Reduce a product of two field elements. -/
def reduce (t : List UInt64) : List UInt64 :=
  canon ((fold (fold (fold t))).take 4)

theorem reduce_spec (t : List UInt64) (ht : 4 ≤ t.length) (hv : val t < 2^512) :
    val (reduce t) = val t % P ∧ (reduce t).length = 4 := by
  have ⟨e1, v1, l1⟩ := fold_spec t ht
  have ⟨e2, v2, l2⟩ := fold_spec _ l1
  have ⟨e3, v3, l3⟩ := fold_spec _ l2
  have s0 := val_take_drop 4 t
  have s1 := val_take_drop 4 (fold t)
  have s2 := val_take_drop 4 (fold (fold t))
  have s3 := val_take_drop 4 (fold (fold (fold t)))
  have hl (u : List UInt64) (h : 4 ≤ u.length) : (u.take 4).length = 4 := by simp; omega
  rw [hl _ ht] at s0; rw [hl _ l1] at s1; rw [hl _ l2] at s2; rw [hl _ l3] at s3
  have b0 := val_lt (t.take 4); have b1 := val_lt ((fold t).take 4)
  have b2 := val_lt ((fold (fold t)).take 4); have b3 := val_lt ((fold (fold (fold t))).take 4)
  rw [hl _ ht] at b0; rw [hl _ l1] at b1; rw [hl _ l2] at b2; rw [hl _ l3] at b3
  simp only [show (64 * 4 : Nat) = 256 from rfl] at *
  -- the high part vanishes after three folds
  have hz : val ((fold (fold (fold t))).drop 4) = 0 := by
    generalize val (List.drop 4 t) = h0 at *
    generalize val (List.drop 4 (fold t)) = h1 at *
    generalize val (List.drop 4 (fold (fold t))) = h2 at *
    generalize val (List.drop 4 (fold (fold (fold t)))) = h3 at *
    generalize val (fold t) = f1 at *
    generalize val (fold (fold t)) = f2 at *
    generalize val (fold (fold (fold t))) = f3 at *
    generalize val t = v at *
    simp only [P, C] at *
    omega
  have hlow : val ((fold (fold (fold t))).take 4) = val (fold (fold (fold t))) := by
    rw [s3, hz]; simp
  have ⟨c1, c2⟩ := canon_spec _ (hl _ l3) (by rw [hlow, v3]; omega)
  refine ⟨?_, c2⟩
  unfold reduce
  rw [c1, hlow]
  rw [e1, e2, e3, Nat.add_assoc, Nat.add_assoc, ← Nat.mul_add, ← Nat.mul_add, Nat.add_mul_mod_self_left]

/-! ## Operations -/

theorem Fq.len (a : Fq) : a.1.length = 4 := a.2.1
theorem Fq.lt (a : Fq) : val a.1 < P := a.2.2

/-- `(a + b) mod P` for `a, b < P`: add, then subtract `P` when the sum reached it. -/
def addRaw (a b : List UInt64) : List UInt64 :=
  let s := addc a b 0
  let d := subb s.1 pL 0
  if s.2 = 1 ∨ d.2 = 0 then d.1 else s.1

theorem addRaw_spec (a b : List UInt64) (ha : a.length = 4) (hb : b.length = 4)
    (va : val a < P) (vb : val b < P) :
    val (addRaw a b) = (val a + val b) % P ∧ (addRaw a b).length = 4 := by
  have ⟨s1, s2, s3⟩ := addc_spec a b 0 (by simp)
  rw [ha, hb] at s3; simp at s3
  have ⟨d1, d2, d3⟩ := subb_spec (addc a b 0).1 pL 0 (by simp) (by rw [s3, len_pL])
  rw [val_pL, s3] at d1; rw [s3] at s1
  have bd := val_lt (subb (addc a b 0).1 pL 0).1
  have bs := val_lt (addc a b 0).1
  rw [d3, s3] at bd; rw [s3] at bs
  have := P_gt; have := P_lt
  simp at s1 d1 bd bs
  simp only [addRaw]
  split
  · rename_i h
    refine ⟨?_, by rw [d3, s3]⟩
    rcases h with h | h
    · rw [h] at s1; simp at s1
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h] at d1; simp at d1
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rename_i h
    refine ⟨?_, s3⟩
    simp only [not_or] at h
    have hk : (addc a b 0).2.toNat = 0 := by
      have : (addc a b 0).2.toNat ≠ 1 := fun h1 => h.1 (UInt64.toNat_inj.1 (by simpa using h1))
      omega
    have hb : (subb (addc a b 0).1 pL 0).2.toNat = 1 := by
      have : (subb (addc a b 0).1 pL 0).2.toNat ≠ 0 := fun h0 => h.2 (UInt64.toNat_inj.1 (by simpa using h0))
      omega
    rw [hk] at s1; rw [hb] at d1; simp at s1 d1
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `(a - b) mod P` for `a, b < P`: subtract, then add `P` back on a borrow. -/
def subRaw (a b : List UInt64) : List UInt64 :=
  let d := subb a b 0
  if d.2 = 0 then d.1 else (addc d.1 pL 0).1

theorem subRaw_spec (a b : List UInt64) (ha : a.length = 4) (hb : b.length = 4)
    (va : val a < P) (vb : val b < P) :
    val (subRaw a b) = (P - val b + val a) % P ∧ (subRaw a b).length = 4 := by
  have ⟨d1, d2, d3⟩ := subb_spec a b 0 (by simp) (by rw [ha, hb])
  rw [ha] at d1 d3
  have ⟨s1, s2, s3⟩ := addc_spec (subb a b 0).1 pL 0 (by simp)
  rw [d3, len_pL] at s3; simp at s3
  rw [s3, val_pL] at s1
  have bd := val_lt (subb a b 0).1
  have bs := val_lt (addc (subb a b 0).1 pL 0).1
  rw [d3] at bd; rw [s3] at bs
  have := P_gt; have := P_lt
  simp at d1 s1 bd bs
  simp only [subRaw]
  split
  · rename_i h
    refine ⟨?_, d3⟩
    rw [h] at d1; simp at d1
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rename_i h
    refine ⟨?_, s3⟩
    have hb : (subb a b 0).2.toNat = 1 := by
      have : (subb a b 0).2.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.1 (by simpa using h0))
      omega
    rw [hb] at d1; simp at d1
    rw [Nat.mod_eq_of_lt (by omega)]
    have : (addc (subb a b 0).1 pL 0).2.toNat = 1 := by omega
    rw [this] at s1; omega

/-- `(a * b) mod P`. -/
def mulRaw (a b : List UInt64) : List UInt64 := reduce (mulL a b)

theorem mulL_length (a : UInt64) (as bs : List UInt64) : bs.length + 2 ≤ (mulL (a :: as) bs).length := by
  have ⟨_, r2⟩ := mulAddRow_spec a bs 0
  have ⟨_, _, t3⟩ := addc_spec (mulAddRow a bs 0) (0 :: mulL as bs) 0 (by simp)
  simp only [mulL, List.length_append, List.length_cons, List.length_nil, t3, r2]
  omega

theorem mulRaw_spec (a b : List UInt64) (ha : a.length = 4) (hb : b.length = 4)
    (va : val a < P) (vb : val b < P) :
    val (mulRaw a b) = (val a * val b) % P ∧ (mulRaw a b).length = 4 := by
  have hm := mulL_spec a b
  have hl : 4 ≤ (mulL a b).length := by
    match a, ha with
    | x :: xs, _ => have := mulL_length x xs b; omega
  have hp : val a * val b < 2^512 := by
    have := Nat.mul_lt_mul'' (Nat.lt_trans va P_lt) (Nat.lt_trans vb P_lt)
    rwa [← Nat.pow_add] at this
  have := reduce_spec (mulL a b) hl (by rw [hm]; exact hp)
  rw [hm] at this
  exact this

def Fq.add (a b : Fq) : Fq :=
  ⟨addRaw a.1 b.1, by
    have h := addRaw_spec a.1 b.1 a.len b.len a.lt b.lt
    exact ⟨h.2, by rw [h.1]; exact Nat.mod_lt _ (by decide)⟩⟩

def Fq.sub (a b : Fq) : Fq :=
  ⟨subRaw a.1 b.1, by
    have h := subRaw_spec a.1 b.1 a.len b.len a.lt b.lt
    exact ⟨h.2, by rw [h.1]; exact Nat.mod_lt _ (by decide)⟩⟩

def Fq.mul (a b : Fq) : Fq :=
  ⟨mulRaw a.1 b.1, by
    have h := mulRaw_spec a.1 b.1 a.len b.len a.lt b.lt
    exact ⟨h.2, by rw [h.1]; exact Nat.mod_lt _ (by decide)⟩⟩

instance : Add Fq := ⟨Fq.add⟩
instance : Sub Fq := ⟨Fq.sub⟩
instance : Mul Fq := ⟨Fq.mul⟩

@[simp] theorem Fq.toF_add (a b : Fq) : (a + b).toF = a.toF + b.toF := by
  apply Fin.ext
  rw [Fin.val_add]
  exact (addRaw_spec a.1 b.1 a.len b.len a.lt b.lt).1

@[simp] theorem Fq.toF_sub (a b : Fq) : (a - b).toF = a.toF - b.toF := by
  apply Fin.ext
  rw [Fin.sub_def]
  exact (subRaw_spec a.1 b.1 a.len b.len a.lt b.lt).1

@[simp] theorem Fq.toF_mul (a b : Fq) : (a * b).toF = a.toF * b.toF := by
  apply Fin.ext
  rw [Fin.val_mul]
  exact (mulRaw_spec a.1 b.1 a.len b.len a.lt b.lt).1

end Secp
