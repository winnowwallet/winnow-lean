import Secp.Der

/-! # Strict BIP 66 DER canonicality (`Secp/Der.lean`)

1. `der_size_bounds`: `8 ≤ (der sig).size ∧ (der sig).size ≤ 72` for every `sig`.
2. `parseDer_der`: for any 64-byte `sig`, `parseDer (der sig) = some sig` (round-trip completeness).
3. `der_parseDer`: if `parseDer b = some sig`, then `sig.size = 64` and `der sig = b` (strict BIP 66
   canonicality: no non-canonical encoding is accepted). -/

namespace Secp.Ecdsa

private theorem toList_loop (bs : ByteArray) : ∀ (n i : Nat) (r : List UInt8), i + n = bs.size →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have len : bs.data.toList.length = bs.size := Array.length_toList
  intro n
  induction n with
  | zero =>
    intro i r h
    have : i = bs.size := by omega
    subst this
    rw [ByteArray.toList.loop]
    simp only [Nat.lt_irrefl, ↓reduceIte]
    rw [List.drop_of_length_le (Nat.le_of_eq len), List.append_nil]
  | succ n ih =>
    intro i r h
    have lt : i < bs.size := by omega
    rw [ByteArray.toList.loop]
    simp only [lt, ↓reduceIte]
    have cons : bs.data.toList.drop i = bs.data.toList[i]'(len ▸ lt) :: bs.data.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (len ▸ lt)
    rw [ih (i + 1) _ (by omega), cons, List.reverse_cons, List.append_assoc]
    have same : bs.get! i = bs.data.toList[i]'(len ▸ lt) := by
      show bs.data[i]! = _
      rw [getElem!_pos bs.data i lt]
      rfl
    rw [same]
    simp

private theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop bs bs.size 0 [] (by omega)]
  rfl

@[simp] private theorem data_toList_length (b : ByteArray) : b.data.toList.length = b.size := Array.length_toList

@[simp] private theorem guard_true : (guard True : Option Unit) = some () := rfl

@[simp] private theorem guard_false : (guard False : Option Unit) = none := rfl

@[simp] private theorem option_some_bind {α β} (x : α) (f : α → Option β) : Option.bind (some x) f = f x := rfl

@[simp] private theorem empty_data_toList : ByteArray.empty.data.toList = [] := rfl

private theorem ba_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b; simp_all

private theorem extract_toList (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = (b.data.toList.drop s).take (e - s) := by
  apply List.ext_getElem
  · rw [data_toList_length, ByteArray.size_extract, List.length_take, List.length_drop, data_toList_length]
    omega
  · intro i h1 h2
    rw [data_toList_length, ByteArray.size_extract] at h1
    rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_extract,
        List.getElem_take, List.getElem_drop, Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

private theorem append_toList (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  apply List.ext_getElem
  · rw [data_toList_length, ByteArray.size_append, List.length_append, data_toList_length, data_toList_length]
  · intro i h1 h2
    rw [data_toList_length, ByteArray.size_append] at h1
    have hal : a.data.toList.length = a.size := data_toList_length a
    rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
    by_cases hi : i < a.size
    · rw [ByteArray.getElem_append_left hi, List.getElem_append_left (by omega),
          Array.getElem_toList, ByteArray.getElem_eq_getElem_data]
    · rw [ByteArray.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp only [hal, Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

private theorem mk_toList (a : Array UInt8) : (ByteArray.mk a).data.toList = a.toList := rfl

private theorem dropWhile_length_le {α} (p : α → Bool) (l : List α) : (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.dropWhile_cons]
    split
    · exact Nat.le_trans ih (Nat.le_succ _)
    · simp

private theorem dropWhile_head_false {α} (p : α → Bool) : ∀ {l : List α} {x : α} {xs : List α},
    l.dropWhile p = x :: xs → p x = false
  | [], _, _, h => nomatch h
  | y :: ys, x, xs, h => by
    simp only [List.dropWhile_cons] at h
    split at h
    · exact dropWhile_head_false p h
    · rename_i hfy
      injection h with hx _
      subst hx
      simpa using hfy

private theorem replicate_zero_append_dropWhile : ∀ (l : List UInt8),
    List.replicate (l.length - (l.dropWhile (· == 0)).length) (0 : UInt8) ++ l.dropWhile (· == 0) = l
  | [] => rfl
  | x :: xs => by
    simp only [List.dropWhile_cons]
    by_cases hx : (x == 0) = true
    · simp only [hx, ↓reduceIte, List.length_cons]
      have hle := dropWhile_length_le (· == 0) xs
      have hsub : xs.length + 1 - (xs.dropWhile (· == 0)).length =
          (xs.length - (xs.dropWhile (· == 0)).length) + 1 := by omega
      rw [hsub, List.replicate_succ, List.cons_append, replicate_zero_append_dropWhile xs]
      have hx0 : x = 0 := beq_iff_eq.mp hx
      rw [hx0]
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.sub_self, List.replicate_zero,
        List.nil_append]

private theorem high_bit_grid : ∀ (hi lo : Fin 16),
    let x : UInt8 := UInt8.ofNat (16 * hi.val + lo.val)
    (x &&& 0x80 == 0) = decide (x < 0x80) ∧ (x &&& 0x80 != 0) = decide (x ≥ 0x80) := by
  decide

private theorem uint8_decomp (x : UInt8) : UInt8.ofNat (16 * (x.toNat / 16) + x.toNat % 16) = x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat']
  have := x.toNat_lt
  omega

private theorem high_bit_iff (x : UInt8) : (x &&& 0x80 == 0) = decide (x < 0x80) := by
  have hx := x.toNat_lt
  have h := (high_bit_grid ⟨x.toNat / 16, by omega⟩ ⟨x.toNat % 16, by omega⟩).1
  simpa only [uint8_decomp x] using h

private theorem high_bit_ne_zero_iff (x : UInt8) : (x &&& 0x80 != 0) = decide (x ≥ 0x80) := by
  have hx := x.toNat_lt
  have h := (high_bit_grid ⟨x.toNat / 16, by omega⟩ ⟨x.toNat % 16, by omega⟩).2
  simpa only [uint8_decomp x] using h

theorem derInteger_size_bounds (number : ByteArray) (h : number.size ≤ 32) :
    3 ≤ (derInteger number).size ∧ (derInteger number).size ≤ 35 := by
  simp only [derInteger, ByteArray.size]
  have hlen : number.toList.length ≤ 32 := by rw [toList_eq, data_toList_length]; exact h
  have hdw := dropWhile_length_le (· == 0) number.toList
  cases hdigits : number.toList.dropWhile (· == 0) with
  | nil => simp
  | cons first rest =>
    rw [hdigits] at hdw
    simp only [List.length_cons] at hdw
    by_cases hf : first ≥ 0x80 <;> (simp [hf]; try omega)

/-- Every `der` output is between 8 and 72 bytes. -/
theorem der_size_bounds (sig : ByteArray) : 8 ≤ (der sig).size ∧ (der sig).size ≤ 72 := by
  simp only [der]
  have hr : (sig.extract 0 32).size ≤ 32 := by rw [ByteArray.size_extract]; omega
  have hs : (sig.extract 32 64).size ≤ 32 := by rw [ByteArray.size_extract]; omega
  obtain ⟨rlo, rhi⟩ := derInteger_size_bounds _ hr
  obtain ⟨slo, shi⟩ := derInteger_size_bounds _ hs
  simp only [ByteArray.size_append]
  have hhdr : (ByteArray.mk #[0x30, ((derInteger (sig.extract 0 32)).size + (derInteger (sig.extract 32 64)).size).toUInt8]).size = 2 := rfl
  rw [hhdr]
  omega

/-- `parseDerInteger` reads a `derInteger` even when followed by arbitrary trailing bytes `rest`. -/
theorem parseDerInteger_derInteger (num rest : ByteArray) (hnum : num.size = 32) (off : Nat)
    (pre : ByteArray) (hpre : pre.size = off) :
    parseDerInteger (pre ++ derInteger num ++ rest) off = some (num, off + (derInteger num).size) := by
  have hlen_num : num.toList.length = 32 := by rw [toList_eq, data_toList_length, hnum]
  have hdw_le : (num.toList.dropWhile (· == 0)).length ≤ 32 := by
    have := dropWhile_length_le (· == 0) num.toList; omega
  let digits := num.toList.dropWhile (· == 0)
  let body : List UInt8 := match digits with
    | [] => [0]
    | first :: _ => if first ≥ 0x80 then 0 :: digits else digits
  have hder_list : (derInteger num).data.toList = 0x02 :: body.length.toUInt8 :: body := by
    dsimp only [derInteger, digits, body]
    cases num.toList.dropWhile (· == 0) with
    | nil => simp
    | cons first tail => by_cases hf : first ≥ 0x80 <;> simp [hf]
  have hbody_bounds : 1 ≤ body.length ∧ body.length ≤ 33 := by
    dsimp only [body, digits]
    cases hd : num.toList.dropWhile (· == 0) with
    | nil => simp
    | cons f rs =>
      rw [hd] at hdw_le; simp only [List.length_cons] at hdw_le
      by_cases hf : f ≥ 0x80 <;> (simp [hf]; try omega)
  have hder_size : (derInteger num).size = 2 + body.length := by
    have : (derInteger num).data.toList.length = (derInteger num).size := data_toList_length _
    rw [← this, hder_list]; simp; omega
  let full := pre ++ derInteger num ++ rest
  have hfull_list : full.data.toList = pre.data.toList ++ (0x02 :: body.length.toUInt8 :: body) ++ rest.data.toList := by
    simp only [full, append_toList, hder_list]
  have hfull_size : full.size = off + 2 + body.length + rest.size := by
    have : full.data.toList.length = full.size := data_toList_length _
    rw [← this, hfull_list, List.length_append, List.length_append, data_toList_length, data_toList_length, hpre]
    simp; omega
  have get_at (k : Nat) (hk : k < 2 + body.length) :
      full[off + k]'(by omega) = (0x02 :: body.length.toUInt8 :: body)[k]'(by simp; omega) := by
    rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
    simp only [hfull_list, List.append_assoc]
    rw [List.getElem_append_right (by rw [data_toList_length, hpre]; omega)]
    have hidx : off + k - pre.data.toList.length = k := by rw [data_toList_length, hpre]; omega
    simp only [hidx]
    rw [List.getElem_append_left (by simp; omega)]
  have hextract_body : full.extract (off + 2) (off + 2 + body.length) = ⟨body.toArray⟩ := by
    apply ba_ext
    rw [extract_toList, hfull_list, List.append_assoc, List.drop_append]
    have hplen : pre.data.toList.length = off := by rw [data_toList_length, hpre]
    rw [List.drop_of_length_le (by omega), List.nil_append, show off + 2 - pre.data.toList.length = 2 by omega]
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero,
      show off + 2 + body.length - (off + 2) = body.length by omega]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (Nat.le_refl _)]
  have hextract_tail (hgt : 1 < body.length) :
      full.extract (off + 3) (off + 2 + body.length) = ⟨(body.drop 1).toArray⟩ := by
    apply ba_ext
    rw [extract_toList, hfull_list, List.append_assoc, List.drop_append]
    have hplen : pre.data.toList.length = off := by rw [data_toList_length, hpre]
    rw [List.drop_of_length_le (by omega), List.nil_append, show off + 3 - pre.data.toList.length = 3 by omega]
    cases hb : body with
    | nil => rw [hb] at hgt; exact absurd hgt (by decide)
    | cons hd tl =>
      simp only [List.length_cons, List.cons_append, List.drop_succ_cons, List.drop_zero]
      have hsub : off + 2 + (tl.length + 1) - (off + 3) = tl.length := by omega
      rw [hsub, List.take_append_of_le_length (by omega), List.take_of_length_le (Nat.le_refl _)]
  change parseDerInteger full off = _
  unfold parseDerInteger
  have h1 : off + 2 ≤ full.size := by omega
  simp only [h1, ↓reduceDIte]
  have hb_tag : full[off]'(by omega) = 0x02 := by simpa using get_at 0 (by omega)
  have hb_len : (full[off + 1]'(by omega)).toNat = body.length := by
    have := get_at 1 (by omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this
    rw [this, UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  -- Case split on `digits = num.toList.dropWhile (· == 0)` BEFORE substituting `hb_len` into dependent indices
  dsimp only [body, digits] at get_at hextract_body hextract_tail hder_size hb_len hfull_size
  cases hd : num.toList.dropWhile (· == 0) with
  | nil =>
    simp only [hd] at get_at hextract_body hder_size hb_len hfull_size
    have h2 : 1 ≤ ([0] : List UInt8).length ∧ off + 2 + ([0] : List UInt8).length ≤ full.size := ⟨by simp, by simp at hfull_size; omega⟩
    simp only [hb_tag, beq_self_eq_true, Option.pure_def, Option.bind_eq_bind, guard_true, option_some_bind,
      hb_len, h2.1, h2.2, and_self, ↓reduceDIte]
    have hb0 : full[off + 2]'(by omega) = 0 := by simpa using get_at 2 (by simp)
    simp only [hb0, show ((0 : UInt8) &&& 0x80 == 0) = true from rfl, guard_true, option_some_bind,
      List.length_singleton, Nat.lt_irrefl, ↓reduceDIte, beq_self_eq_true, ↓reduceIte]
    have hempty : full.extract (off + 3) (off + 2 + 1) = ByteArray.empty := by
      apply ba_ext; rw [extract_toList]; simp
    simp only [hempty, ByteArray.size_empty, Nat.zero_le, guard_true, option_some_bind, Nat.sub_zero]
    congr 1; apply Prod.ext
    · apply ba_ext
      have hrep := replicate_zero_append_dropWhile num.toList
      rw [hd, List.append_nil, hlen_num] at hrep
      simp only [List.length_nil, Nat.sub_zero] at hrep
      simp only [append_toList, empty_data_toList, List.append_nil, Array.toList_replicate, hrep, toList_eq]
    · simp at hder_size; omega
  | cons first tail =>
    have hfirst_nz : (first == 0) = false := dropWhile_head_false (· == 0) hd
    rw [hd] at hdw_le
    by_cases hf : first ≥ 0x80
    · simp only [hd, hf, ↓reduceIte] at get_at hextract_body hextract_tail hder_size hb_len hfull_size
      have h2 : 1 ≤ (0 :: first :: tail).length ∧ off + 2 + (0 :: first :: tail).length ≤ full.size :=
        ⟨by simp, by simp only [List.length_cons] at hfull_size ⊢; omega⟩
      simp only [hb_tag, beq_self_eq_true, Option.pure_def, Option.bind_eq_bind, guard_true, option_some_bind,
        hb_len, h2.1, h2.2, and_self, ↓reduceDIte]
      have hb0 : full[off + 2]'(by simp only [List.length_cons] at hfull_size; omega) = 0 := by simpa using get_at 2 (by simp)
      have hb1 : full[off + 3]'(by simp only [List.length_cons] at hfull_size; omega) = first := by
        simpa using get_at 3 (by simp; omega)
      have hgt1 : 1 < (0 :: first :: tail).length := by simp
      have hhi : (first &&& 0x80 != 0) = true := by rw [high_bit_ne_zero_iff]; simpa using hf
      have htail := hextract_tail hgt1
      simp only [List.drop_succ_cons, List.drop_zero] at htail
      simp only [hb0, show ((0 : UInt8) &&& 0x80 == 0) = true from rfl, guard_true, option_some_bind,
        hgt1, ↓reduceDIte, beq_self_eq_true, ↓reduceIte, hb1, hhi, htail]
      have hsz : (ByteArray.mk (first :: tail).toArray).size = (first :: tail).length := by simp [ByteArray.size]
      have hg32 : (guard ((ByteArray.mk (first :: tail).toArray).size ≤ 32) : Option Unit) = some () := by
        simp [guard, hsz]; simp only [List.length_cons] at hdw_le; omega
      rw [hg32, option_some_bind]
      simp only [hsz]
      congr 1; apply Prod.ext
      · apply ba_ext
        have hrep := replicate_zero_append_dropWhile num.toList
        rw [hd, hlen_num, toList_eq] at hrep
        simp only [append_toList, Array.toList_replicate, List.length_cons] at hrep ⊢
        exact hrep
      · simp only [List.length_cons] at hder_size ⊢; omega
    · simp only [hd, hf, ↓reduceIte] at get_at hextract_body hextract_tail hder_size hb_len hfull_size
      have h2 : 1 ≤ (first :: tail).length ∧ off + 2 + (first :: tail).length ≤ full.size :=
        ⟨by simp, by simp only [List.length_cons] at hfull_size ⊢; omega⟩
      simp only [hb_tag, beq_self_eq_true, Option.pure_def, Option.bind_eq_bind, guard_true, option_some_bind,
        hb_len, h2.1, h2.2, and_self, ↓reduceDIte]
      have hb0 : full[off + 2]'(by simp only [List.length_cons] at hfull_size; omega) = first := by simpa using get_at 2 (by simp)
      have hlo : (first &&& 0x80 == 0) = true := by
        rw [high_bit_iff]; simp
        simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at hf ⊢; omega
      simp only [hb0, hlo, guard_true, option_some_bind]
      have hstep : (if h3 : 1 < (first :: tail).length then
            if (first == 0) = true then
              Option.bind (guard ((full[off + 3]'(by simp only [List.length_cons] at hfull_size h3; omega) &&& 0x80 != 0) = true)) fun _ =>
                Option.bind (guard ((if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)).size ≤ 32)) fun _ =>
                  some (ByteArray.mk (Array.replicate (32 - (if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)).size) 0) ++ (if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)), off + 2 + (first :: tail).length)
            else
              Option.bind (guard ((if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)).size ≤ 32)) fun _ =>
                some (ByteArray.mk (Array.replicate (32 - (if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)).size) 0) ++ (if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)), off + 2 + (first :: tail).length)
          else
            Option.bind (guard ((if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)).size ≤ 32)) fun _ =>
              some (ByteArray.mk (Array.replicate (32 - (if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)).size) 0) ++ (if (first == 0) = true then full.extract (off + 3) (off + 2 + (first :: tail).length) else full.extract (off + 2) (off + 2 + (first :: tail).length)), off + 2 + (first :: tail).length)) =
          Option.bind (guard ((full.extract (off + 2) (off + 2 + (first :: tail).length)).size ≤ 32)) fun _ =>
            some (ByteArray.mk (Array.replicate (32 - (full.extract (off + 2) (off + 2 + (first :: tail).length)).size) 0) ++ full.extract (off + 2) (off + 2 + (first :: tail).length), off + 2 + (first :: tail).length) := by
        split <;> simp [hfirst_nz]
      rw [hstep]
      simp only [hextract_body]
      have hsz : (ByteArray.mk (first :: tail).toArray).size = (first :: tail).length := by simp [ByteArray.size]
      have hg32 : (guard ((ByteArray.mk (first :: tail).toArray).size ≤ 32) : Option Unit) = some () := by
        simp [guard, hsz]; simp only [List.length_cons] at hdw_le; omega
      rw [hg32, option_some_bind]
      simp only [hsz]
      congr 1; apply Prod.ext
      · apply ba_ext
        have hrep := replicate_zero_append_dropWhile num.toList
        rw [hd, hlen_num, toList_eq] at hrep
        simp only [append_toList, Array.toList_replicate, List.length_cons] at hrep ⊢
        exact hrep
      · simp only [List.length_cons] at hder_size ⊢; omega

/-- **Round-trip completeness:** every 64-byte `(r, s)` pair encodes to DER that `parseDer` decodes back to `sig`. -/
theorem parseDer_der {sig : ByteArray} (hsig : sig.size = 64) : parseDer (der sig) = some sig := by
  have bounds := der_size_bounds sig
  have hr_sz : (sig.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hs_sz : (sig.extract 32 64).size = 32 := by rw [ByteArray.size_extract]; omega
  obtain ⟨rlo, rhi⟩ := derInteger_size_bounds _ (Nat.le_of_eq hr_sz)
  obtain ⟨slo, shi⟩ := derInteger_size_bounds _ (Nat.le_of_eq hs_sz)
  let r := derInteger (sig.extract 0 32)
  let s := derInteger (sig.extract 32 64)
  let hdr := ByteArray.mk #[0x30, (r.size + s.size).toUInt8]
  have hhdr_sz : hdr.size = 2 := rfl
  have hder_eq : der sig = hdr ++ r ++ s := rfl
  have hder_sz : (der sig).size = 2 + r.size + s.size := by
    simp only [hder_eq, ByteArray.size_append, hhdr_sz]
  unfold parseDer
  simp only [bounds.1, bounds.2, and_self, ↓reduceDIte]
  have hb0 : (der sig)[0]'(by omega) = 0x30 := by
    rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
    simp [hder_eq, hdr]
  have hb1 : ((der sig)[1]'(by omega)).toNat = (der sig).size - 2 := by
    have hget : (der sig)[1]'(by omega) = (r.size + s.size).toUInt8 := by
      rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
      simp [hder_eq, hdr]
    rw [hget, UInt8.toNat_ofNat', hder_sz]
    have : r.size + s.size < 256 := by dsimp [r, s]; omega
    rw [Nat.mod_eq_of_lt this]; omega
  simp only [hb0, hb1, beq_self_eq_true, Bool.and_self, guard_true, Option.pure_def, Option.bind_eq_bind,
    option_some_bind]
  have pr := parseDerInteger_derInteger (sig.extract 0 32) s hr_sz 2 hdr hhdr_sz
  change parseDerInteger (der sig) 2 = some (sig.extract 0 32, 2 + r.size) at pr
  rw [pr]; simp only [option_some_bind]
  have ps := parseDerInteger_derInteger (sig.extract 32 64) ByteArray.empty hs_sz (2 + r.size) (hdr ++ r)
    (by simp [ByteArray.size_append, hhdr_sz])
  have hempty : hdr ++ r ++ s ++ ByteArray.empty = der sig := by
    apply ba_ext; simp only [hder_eq, append_toList, empty_data_toList, List.append_nil]
  rw [hempty] at ps
  change Option.bind (parseDerInteger (der sig) (2 + r.size)) _ = _
  rw [ps]; simp only [option_some_bind]
  have hend : (2 + r.size + s.size == (der sig).size) = true := beq_iff_eq.mpr hder_sz.symm
  dsimp only [r, s] at hend ⊢
  simp only [hend, guard_true, option_some_bind, Option.some.injEq]
  apply ba_ext
  rw [append_toList, extract_toList, extract_toList]
  have hll : sig.data.toList.length = 64 := by rw [data_toList_length, hsig]
  simp only [List.drop_zero, show 64 - 32 = 32 from rfl]
  have htake : (sig.data.toList.drop 32).take 32 = sig.data.toList.drop 32 :=
    List.take_of_length_le (by simp [hll])
  rw [htake, List.take_append_drop]

private theorem dropWhile_replicate_zero_append (k : Nat) (l : List UInt8)
    (hhead : ∀ x xs, l = x :: xs → (x == 0) = false) :
    (List.replicate k (0 : UInt8) ++ l).dropWhile (· == 0) = l := by
  induction k with
  | zero =>
    cases l with
    | nil => rfl
    | cons x xs => simp [hhead x xs rfl]
  | succ k ih =>
    simp [List.replicate_succ, ih]

/-- **Strict BIP 66 integer canonicality:** if `parseDerInteger` accepts at `offset`, the slice
`b[offset .. offset + 2 + length]` is byte-for-byte `derInteger out`, and `out.size = 32`. -/
theorem derInteger_of_parseDerInteger {b : ByteArray} {offset next : Nat} {out : ByteArray}
    (h : parseDerInteger b offset = some (out, next)) :
    out.size = 32 ∧ offset + 3 ≤ next ∧ next ≤ b.size ∧ b.extract offset next = derInteger out := by
  unfold parseDerInteger at h
  have h1 : offset + 2 ≤ b.size := by
    by_cases hc : offset + 2 ≤ b.size
    · exact hc
    · simp [hc] at h
  simp only [h1, ↓reduceDIte, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨_, htag, h⟩ := Option.bind_eq_some_iff.mp h
  have htag0 : b[offset]'(by omega) = 0x02 := by
    by_cases ht : (b[offset]'(by omega) == 0x02) = true
    · exact beq_iff_eq.mp ht
    · simp [ht] at htag
  let length := (b[offset + 1]'(by omega)).toNat
  have h2 : 1 ≤ length ∧ offset + 2 + length ≤ b.size := by
    by_cases hc : 1 ≤ length ∧ offset + 2 + length ≤ b.size
    · exact hc
    · dsimp only [length] at hc; simp [hc] at h
  simp only [show 1 ≤ (b[offset + 1]'(by omega)).toNat from h2.1,
             show offset + 2 + (b[offset + 1]'(by omega)).toNat ≤ b.size from h2.2,
             and_self, ↓reduceDIte] at h
  obtain ⟨_, hb0_hi, h⟩ := Option.bind_eq_some_iff.mp h
  let b0 := b[offset + 2]'(by omega)
  have hb0_lt : b0 < 0x80 := by
    have : (b0 &&& 0x80 == 0) = true := by
      by_cases hc : (b0 &&& 0x80 == 0) = true
      · exact hc
      · dsimp only [b0] at hc; simp [hc] at hb0_hi
    rw [high_bit_iff] at this
    exact of_decide_eq_true this
  let digits := if b0 == 0 then b.extract (offset + 3) (offset + 2 + length)
                else b.extract (offset + 2) (offset + 2 + length)
  have hpad_and_cont :
      (∀ (hgt1 : 1 < length), (b0 == 0) = true → (b[offset + 3]'(by omega) &&& 0x80 != 0) = true) ∧
      Option.bind (guard (digits.size ≤ 32))
        (fun _ => some (ByteArray.mk (Array.replicate (32 - digits.size) 0) ++ digits, offset + 2 + length)) =
        some (out, next) := by
    dsimp only [digits, b0, length]
    by_cases hgt1 : 1 < (b[offset + 1]'(by omega)).toNat
    · simp only [hgt1, ↓reduceDIte] at h
      by_cases hbz : (b[offset + 2]'(by omega) == 0) = true
      · simp only [hbz, ↓reduceIte] at h ⊢
        obtain ⟨_, hp, hc⟩ := Option.bind_eq_some_iff.mp h
        refine ⟨fun _ _ => ?_, hc⟩
        by_cases hhi : (b[offset + 3]'(by omega) &&& 0x80 != 0) = true
        · exact hhi
        · simp [hhi] at hp
      · simp only [hbz, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ⟨fun _ hz => False.elim hz, h⟩
    · simp only [hgt1, ↓reduceDIte] at h
      exact ⟨fun hg _ => absurd hg hgt1, h⟩
  obtain ⟨hpad_chk, h⟩ := hpad_and_cont
  obtain ⟨_, hdig_sz, hret⟩ := Option.bind_eq_some_iff.mp h
  have hdig_le : digits.size ≤ 32 := by
    by_cases hc : digits.size ≤ 32
    · exact hc
    · simp [hc] at hdig_sz
  injection hret with hpair
  have hout : out = ByteArray.mk (Array.replicate (32 - digits.size) 0) ++ digits := (Prod.mk.inj hpair).1.symm
  have hnext : next = offset + 2 + length := (Prod.mk.inj hpair).2.symm
  have hout_sz : out.size = 32 := by
    rw [hout, ByteArray.size_append]
    have : (ByteArray.mk (Array.replicate (32 - digits.size) 0)).size = 32 - digits.size := Array.size_replicate
    rw [this]; omega
  refine ⟨hout_sz, by omega, by omega, ?_⟩
  subst hnext
  have hlen_u8 : length.toUInt8 = b[offset + 1]'(by omega) := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (b[offset + 1]'(by omega)).toNat_lt]
  -- Extract slice structure: `[0x02, b[offset + 1]] ++ b.extract (offset + 2) (offset + 2 + length)`
  have hslice_split : (b.extract offset (offset + 2 + length)).data.toList =
      0x02 :: b[offset + 1]'(by omega) :: (b.extract (offset + 2) (offset + 2 + length)).data.toList := by
    rw [extract_toList, extract_toList]
    have hblen : b.data.toList.length = b.size := Array.length_toList
    have hd0 : b.data.toList.drop offset =
        b[offset]'(by omega) :: b.data.toList.drop (offset + 1) := by
      rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
      exact List.drop_eq_getElem_cons (hblen ▸ show offset < b.size by omega)
    have hd1 : b.data.toList.drop (offset + 1) =
        b[offset + 1]'(by omega) :: b.data.toList.drop (offset + 2) := by
      rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
      exact List.drop_eq_getElem_cons (hblen ▸ show offset + 1 < b.size by omega)
    rw [hd0, hd1, htag0, show offset + 2 + length - offset = length + 2 by omega,
        show offset + 2 + length - (offset + 2) = length by omega]
    rfl
  have hbody_split : (b.extract (offset + 2) (offset + 2 + length)).data.toList =
      b0 :: (b.extract (offset + 3) (offset + 2 + length)).data.toList := by
    rw [extract_toList, extract_toList]
    have hblen : b.data.toList.length = b.size := Array.length_toList
    have hd2 : b.data.toList.drop (offset + 2) =
        b0 :: b.data.toList.drop (offset + 3) := by
      dsimp [b0]; rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
      exact List.drop_eq_getElem_cons (hblen ▸ show offset + 2 < b.size by omega)
    rw [hd2, show offset + 2 + length - (offset + 2) = (length - 1) + 1 by omega,
        show offset + 2 + length - (offset + 3) = length - 1 by omega]
    rfl
  apply ba_ext
  rw [hslice_split]
  by_cases hb0z : (b0 == 0) = true
  · have hb0_eq : b0 = 0 := beq_iff_eq.mp hb0z
    have hdig_eq : digits = b.extract (offset + 3) (offset + 2 + length) := by simp [digits, hb0z]
    by_cases hgt1 : 1 < length
    · -- Leading 0x00 with `length > 1`: `b[offset + 3] ≥ 0x80`, so `digits` starts with `b1 ≥ 0x80` (nonzero!)
      let b1 := b[offset + 3]'(by omega)
      have hb1_ge : b1 ≥ 0x80 := by
        have : (b1 &&& 0x80 != 0) = true := hpad_chk hgt1 hb0z
        rw [high_bit_ne_zero_iff] at this
        exact of_decide_eq_true this
      have htail_cons : digits.data.toList = b1 :: (b.extract (offset + 4) (offset + 2 + length)).data.toList := by
        rw [hdig_eq, extract_toList, extract_toList]
        have hblen : b.data.toList.length = b.size := Array.length_toList
        have hd3 : b.data.toList.drop (offset + 3) =
            b1 :: b.data.toList.drop (offset + 4) := by
          dsimp [b1]; rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
          exact List.drop_eq_getElem_cons (hblen ▸ show offset + 3 < b.size by omega)
        rw [hd3, show offset + 2 + length - (offset + 3) = (length - 2) + 1 by omega,
            show offset + 2 + length - (offset + 4) = length - 2 by omega]
        rfl
      have hdw : out.toList.dropWhile (· == 0) = digits.data.toList := by
        rw [toList_eq, hout, append_toList, mk_toList, Array.toList_replicate]
        apply dropWhile_replicate_zero_append
        intro x xs hxs
        rw [htail_cons] at hxs
        injection hxs with hx _
        subst hx
        apply beq_false_of_ne; intro h0; rw [h0] at hb1_ge; contradiction
      have hdig_len : digits.data.toList.length = length - 1 := by
        rw [hdig_eq, extract_toList, List.length_take, List.length_drop, data_toList_length]
        omega
      simp only [derInteger, hdw, htail_cons, hb1_ge, ↓reduceIte, Array.toList_append]
      have hbl : (0 :: b1 :: (b.extract (offset + 4) (offset + 2 + length)).data.toList).length = length := by
        have := hdig_len; rw [htail_cons] at this; simp at this ⊢; omega
      rw [hbl, hlen_u8, hbody_split, hb0_eq, ← hdig_eq, htail_cons]
      rfl
    · -- `length = 1` and `b0 = 0`: `digits = empty`, `out = 32 zeros`, `derInteger out = [0x02, 0x01, 0x00]`
      have hlen1 : length = 1 := by omega
      have hdig_empty : digits.data.toList = [] := by
        rw [hdig_eq, extract_toList, show offset + 2 + length - (offset + 3) = 0 by omega, List.take_zero]
      have hdw : out.toList.dropWhile (· == 0) = [] := by
        rw [toList_eq, hout, append_toList, mk_toList, Array.toList_replicate, hdig_empty]
        exact dropWhile_replicate_zero_append _ [] (fun _ _ h => nomatch h)
      simp only [derInteger, hdw, Array.toList_append, hbody_split, hb0_eq, ← hdig_eq, hdig_empty]
      have hb1_eq : b[offset + 1]'(by omega) = 1 := by
        rw [← hlen_u8, hlen1]; rfl
      rw [hb1_eq]; rfl
  · -- `b0 ≠ 0` and `b0 < 0x80`: `digits` starts with `b0`
    have hb0_ne : (b0 == 0) = false := Bool.eq_false_iff.mpr hb0z
    have hdig_eq : digits = b.extract (offset + 2) (offset + 2 + length) := by simp [digits, hb0_ne]
    have hdig_cons : digits.data.toList = b0 :: (b.extract (offset + 3) (offset + 2 + length)).data.toList := by
      rw [hdig_eq, hbody_split]
    have hdw : out.toList.dropWhile (· == 0) = digits.data.toList := by
      rw [toList_eq, hout, append_toList, mk_toList, Array.toList_replicate]
      apply dropWhile_replicate_zero_append
      intro x xs hxs
      rw [hdig_cons] at hxs
      injection hxs with hx _
      subst hx
      exact hb0_ne
    have hnot_ge : ¬ (b0 ≥ 0x80) := by
      simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at hb0_lt ⊢; omega
    have hdig_len : digits.data.toList.length = length := by
      rw [hdig_eq, extract_toList, List.length_take, List.length_drop, data_toList_length]; omega
    simp only [derInteger, hdw, hdig_cons, hnot_ge, ↓reduceIte, Array.toList_append]
    have hbl : (b0 :: (b.extract (offset + 3) (offset + 2 + length)).data.toList).length = length := by
      rw [← hdig_cons]; exact hdig_len
    rw [hbl, hlen_u8, hbody_split]
    rfl

/-- **Strict BIP 66 sequence canonicality:** any buffer accepted by `parseDer` is byte-identical to `der sig`,
and `sig` is 64 bytes. -/
theorem der_parseDer {b sig : ByteArray} (h : parseDer b = some sig) :
    sig.size = 64 ∧ der sig = b ∧ 8 ≤ b.size ∧ b.size ≤ 72 := by
  unfold parseDer at h
  have hbounds : 8 ≤ b.size ∧ b.size ≤ 72 := by
    by_cases hc : 8 ≤ b.size ∧ b.size ≤ 72
    · exact hc
    · simp [hc] at h
  simp only [hbounds.1, hbounds.2, and_self, ↓reduceDIte, Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨_, hhdr, h⟩ := Option.bind_eq_some_iff.mp h
  have hhdr_ok : b[0]'(by omega) = 0x30 ∧ (b[1]'(by omega)).toNat = b.size - 2 := by
    by_cases hc : (b[0]'(by omega) == 0x30 && (b[1]'(by omega)).toNat == b.size - 2) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc
    · simp [hc] at hhdr
  obtain ⟨⟨r, afterR⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨s, afterS⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, hend, hret⟩ := Option.bind_eq_some_iff.mp h
  have hafterS : afterS = b.size := by
    by_cases hc : (afterS == b.size) = true
    · exact beq_iff_eq.mp hc
    · simp [hc] at hend
  injection hret with hsig_eq
  subst hsig_eq hafterS
  obtain ⟨hr_sz, hr_lo, hr_hi, hr_slice⟩ := derInteger_of_parseDerInteger hr
  obtain ⟨hs_sz, hs_lo, hs_hi, hs_slice⟩ := derInteger_of_parseDerInteger hs
  have hsig_sz : (r ++ s).size = 64 := by rw [ByteArray.size_append, hr_sz, hs_sz]
  have hex_r : (r ++ s).extract 0 32 = r := by
    apply ba_ext
    rw [extract_toList, append_toList, List.drop_zero, show 32 - 0 = 32 from rfl]
    have hrl : r.data.toList.length = 32 := by rw [data_toList_length, hr_sz]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hex_s : (r ++ s).extract 32 64 = s := by
    apply ba_ext
    rw [extract_toList, append_toList]
    have hrl : r.data.toList.length = 32 := by rw [data_toList_length, hr_sz]
    have hsl : s.data.toList.length = 32 := by rw [data_toList_length, hs_sz]
    rw [List.drop_append, List.drop_of_length_le (by omega), List.nil_append, hrl, Nat.sub_self, List.drop_zero,
        show 64 - 32 = 32 from rfl, List.take_of_length_le (by omega)]
  refine ⟨hsig_sz, ?_, hbounds.1, hbounds.2⟩
  simp only [der, hex_r, hex_s, ← hr_slice, ← hs_slice]
  have hsz_r : (b.extract 2 afterR).size = afterR - 2 := by rw [ByteArray.size_extract]; omega
  have hsz_s : (b.extract afterR b.size).size = b.size - afterR := by rw [ByteArray.size_extract]; omega
  have hb1_u8 : ((b.extract 2 afterR).size + (b.extract afterR b.size).size).toUInt8 = b[1]'(by omega) := by
    rw [hsz_r, hsz_s, show afterR - 2 + (b.size - afterR) = b.size - 2 by omega, ← hhdr_ok.2]
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (b[1]'(by omega)).toNat_lt]
  rw [hb1_u8]
  apply ba_ext
  rw [append_toList, append_toList, mk_toList, extract_toList, extract_toList]
  have hbl : b.data.toList.length = b.size := Array.length_toList
  have ht2 : (b.data.toList.drop 2).take (afterR - 2) ++ (b.data.toList.drop afterR).take (b.size - afterR) =
      b.data.toList.drop 2 := by
    have htake_end : (b.data.toList.drop afterR).take (b.size - afterR) = b.data.toList.drop afterR :=
      List.take_of_length_le (by simp [hbl])
    rw [htake_end]
    have hdrop_add : b.data.toList.drop afterR = (b.data.toList.drop 2).drop (afterR - 2) := by
      rw [List.drop_drop, show 2 + (afterR - 2) = afterR by omega]
    rw [hdrop_add, List.take_append_drop]
  rw [List.append_assoc, ht2]
  have hd0 : b.data.toList = b[0]'(by omega) :: b[1]'(by omega) :: b.data.toList.drop 2 := by
    have c0 : b.data.toList = b[0]'(by omega) :: b.data.toList.drop 1 := by
      rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
      exact List.drop_eq_getElem_cons (hbl ▸ show 0 < b.size by omega)
    have c1 : b.data.toList.drop 1 = b[1]'(by omega) :: b.data.toList.drop 2 := by
      rw [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
      exact List.drop_eq_getElem_cons (hbl ▸ show 1 < b.size by omega)
    exact c0.trans (congrArg (b[0]'(by omega) :: ·) c1)
  rw [← hhdr_ok.1]
  exact hd0.symm

end Secp.Ecdsa
