import SecpCt.ScalarProofs
import Secp.Bytes

/-! # Bytes and words

Reading: the field element and the scalar that thirty-two bytes stand for are the number those bytes spell,
most significant first, as winnow reads it (`Secp.fromBE`), modulo P and modulo N (`Fe.ofBytes_spec`,
`Sc.ofBytes_spec`). On the way: eight bytes put together by shifting are the number they spell
(`word_of_bytes`), an array of thirty-two bytes can be written out as thirty-two bytes (`bytes32`), and
folding over a byte array is folding over the list of its bytes (`foldl_bytes`), which Lean's library does
not state.

Writing: `Fe.bytes` and `Sc.bytes` give the thirty-two bytes winnow writes for the same number
(`Secp.toBE32`; `Fe.bytes_spec`, `Sc.bytes_spec`). -/

namespace SecpCt

/-- Or-ing in the next byte below what is already there is appending it. -/
theorem or_step (p b i j : Nat) (hj : j = i + 8) (hb : b < 256) : p <<< j ||| b <<< i = (p * 256 + b) <<< i := by
  subst hj
  rw [show i + 8 = 8 + i from Nat.add_comm _ _, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib,
    ← Nat.shiftLeft_add_eq_or_of_lt (show b < 2 ^ 8 from hb), Nat.shiftLeft_eq p 8]

/-- Eight bytes put together by shifting and or-ing are the number they spell, most significant first. -/
theorem word_of_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    ((b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) ||| (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32) |||
      (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) ||| (b6.toUInt64 <<< 8) ||| b7.toUInt64).toNat =
    ((((((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat) * 256 + b4.toNat) * 256 + b5.toNat) * 256
      + b6.toNat) * 256 + b7.toNat := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  have fits (b : UInt8) (s : Nat) (hs : s ≤ 56) : b.toNat <<< s % 2 ^ 64 = b.toNat <<< s := by
    apply Nat.mod_eq_of_lt
    have := b.toNat_lt
    rw [Nat.shiftLeft_eq]
    calc b.toNat * 2 ^ s < 2 ^ 8 * 2 ^ s := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos s)
      _ = 2 ^ (8 + s) := (Nat.pow_add 2 8 s).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    show (56 : UInt64).toNat % 64 = 56 from rfl, show (48 : UInt64).toNat % 64 = 48 from rfl,
    show (40 : UInt64).toNat % 64 = 40 from rfl, show (32 : UInt64).toNat % 64 = 32 from rfl,
    show (24 : UInt64).toNat % 64 = 24 from rfl, show (16 : UInt64).toNat % 64 = 16 from rfl,
    show (8 : UInt64).toNat % 64 = 8 from rfl]
  rw [fits b0 56 (by decide), fits b1 48 (by decide), fits b2 40 (by decide), fits b3 32 (by decide),
    fits b4 24 (by decide), fits b5 16 (by decide), fits b6 8 (by decide)]
  rw [or_step _ _ 48 56 rfl h1, or_step _ _ 40 48 rfl h2, or_step _ _ 32 40 rfl h3, or_step _ _ 24 32 rfl h4,
    or_step _ _ 16 24 rfl h5, or_step _ _ 8 16 rfl h6,
    ← Nat.shiftLeft_add_eq_or_of_lt (show b7.toNat < 2 ^ 8 from h7), Nat.shiftLeft_eq]
theorem list_split {α : Type} (l : List α) (n : Nat) (h : l.length = n + 1) : ∃ a t, l = a :: t ∧ t.length = n := by
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

/-- Thirty-two bytes are thirty-two bytes: an array of that size, written out. -/
theorem bytes32 (b : ByteArray) (h : b.size = 32) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : UInt8, b = ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ := by
  obtain ⟨⟨l0⟩⟩ := b
  have h0 : l0.length = 32 := h
  obtain ⟨b0, l1, rfl, h1⟩ := list_split l0 31 h0
  obtain ⟨b1, l2, rfl, h2⟩ := list_split l1 30 h1
  obtain ⟨b2, l3, rfl, h3⟩ := list_split l2 29 h2
  obtain ⟨b3, l4, rfl, h4⟩ := list_split l3 28 h3
  obtain ⟨b4, l5, rfl, h5⟩ := list_split l4 27 h4
  obtain ⟨b5, l6, rfl, h6⟩ := list_split l5 26 h5
  obtain ⟨b6, l7, rfl, h7⟩ := list_split l6 25 h6
  obtain ⟨b7, l8, rfl, h8⟩ := list_split l7 24 h7
  obtain ⟨b8, l9, rfl, h9⟩ := list_split l8 23 h8
  obtain ⟨b9, l10, rfl, h10⟩ := list_split l9 22 h9
  obtain ⟨b10, l11, rfl, h11⟩ := list_split l10 21 h10
  obtain ⟨b11, l12, rfl, h12⟩ := list_split l11 20 h11
  obtain ⟨b12, l13, rfl, h13⟩ := list_split l12 19 h12
  obtain ⟨b13, l14, rfl, h14⟩ := list_split l13 18 h13
  obtain ⟨b14, l15, rfl, h15⟩ := list_split l14 17 h14
  obtain ⟨b15, l16, rfl, h16⟩ := list_split l15 16 h15
  obtain ⟨b16, l17, rfl, h17⟩ := list_split l16 15 h16
  obtain ⟨b17, l18, rfl, h18⟩ := list_split l17 14 h17
  obtain ⟨b18, l19, rfl, h19⟩ := list_split l18 13 h18
  obtain ⟨b19, l20, rfl, h20⟩ := list_split l19 12 h19
  obtain ⟨b20, l21, rfl, h21⟩ := list_split l20 11 h20
  obtain ⟨b21, l22, rfl, h22⟩ := list_split l21 10 h21
  obtain ⟨b22, l23, rfl, h23⟩ := list_split l22 9 h22
  obtain ⟨b23, l24, rfl, h24⟩ := list_split l23 8 h23
  obtain ⟨b24, l25, rfl, h25⟩ := list_split l24 7 h24
  obtain ⟨b25, l26, rfl, h26⟩ := list_split l25 6 h25
  obtain ⟨b26, l27, rfl, h27⟩ := list_split l26 5 h26
  obtain ⟨b27, l28, rfl, h28⟩ := list_split l27 4 h27
  obtain ⟨b28, l29, rfl, h29⟩ := list_split l28 3 h28
  obtain ⟨b29, l30, rfl, h30⟩ := list_split l29 2 h29
  obtain ⟨b30, l31, rfl, h31⟩ := list_split l30 1 h30
  obtain ⟨b31, l32, rfl, h32⟩ := list_split l31 0 h31
  have : l32 = [] := List.length_eq_zero_iff.mp h32
  subst this
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩

/-! ## Reading a number from bytes -/

theorem foldl_loop {β : Type} (f : β → UInt8 → β) (as : ByteArray) :
    ∀ (i j : Nat) (b : β), j + i = as.size →
      ByteArray.foldlM.loop (m := Id) f as as.size (Nat.le_refl _) i j b = (as.data.toList.drop j).foldl f b := by
  have len : as.data.toList.length = as.size := Array.length_toList
  intro i
  induction i with
  | zero =>
    intro j b h
    have : j = as.size := by omega
    subst this
    unfold ByteArray.foldlM.loop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    rw [List.drop_of_length_le (Nat.le_of_eq len)]
    rfl
  | succ i ih =>
    intro j b h
    have lt : j < as.size := by omega
    unfold ByteArray.foldlM.loop
    simp only [lt, ↓reduceDIte]
    have step := ih (j + 1) (f b as[j]) (by omega)
    have cons : as.data.toList.drop j = as[j] :: as.data.toList.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (len ▸ lt)]
      rfl
    rw [cons, List.foldl_cons]
    exact step

/-- Folding over a byte array is folding over the list of its bytes. -/
theorem foldl_bytes {β : Type} (f : β → UInt8 → β) (init : β) (as : ByteArray) :
    as.foldl f init = as.data.toList.foldl f init := by
  have h := foldl_loop f as as.size 0 init (by omega)
  simp only [ByteArray.foldl, ByteArray.foldlM, Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  exact h

/-- The number thirty-two bytes spell, most significant first, as winnow reads it, is the four words
`wordAt` takes from them. -/
theorem fromBE_words (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : UInt8) :
    Secp.fromBE ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ =
      value (wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 24) (wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 16)
        (wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 8) (wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 0) := by
  have w0 := word_of_bytes b0 b1 b2 b3 b4 b5 b6 b7
  have w1 := word_of_bytes b8 b9 b10 b11 b12 b13 b14 b15
  have w2 := word_of_bytes b16 b17 b18 b19 b20 b21 b22 b23
  have w3 := word_of_bytes b24 b25 b26 b27 b28 b29 b30 b31
  have e0 : wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 0 = (b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) ||| (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32) ||| (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) ||| (b6.toUInt64 <<< 8) ||| b7.toUInt64 := rfl
  have e1 : wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 8 = (b8.toUInt64 <<< 56) ||| (b9.toUInt64 <<< 48) ||| (b10.toUInt64 <<< 40) ||| (b11.toUInt64 <<< 32) ||| (b12.toUInt64 <<< 24) ||| (b13.toUInt64 <<< 16) ||| (b14.toUInt64 <<< 8) ||| b15.toUInt64 := rfl
  have e2 : wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 16 = (b16.toUInt64 <<< 56) ||| (b17.toUInt64 <<< 48) ||| (b18.toUInt64 <<< 40) ||| (b19.toUInt64 <<< 32) ||| (b20.toUInt64 <<< 24) ||| (b21.toUInt64 <<< 16) ||| (b22.toUInt64 <<< 8) ||| b23.toUInt64 := rfl
  have e3 : wordAt ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]⟩ 24 = (b24.toUInt64 <<< 56) ||| (b25.toUInt64 <<< 48) ||| (b26.toUInt64 <<< 40) ||| (b27.toUInt64 <<< 32) ||| (b28.toUInt64 <<< 24) ||| (b29.toUInt64 <<< 16) ||| (b30.toUInt64 <<< 8) ||| b31.toUInt64 := rfl
  rw [Secp.fromBE, foldl_bytes, e0, e1, e2, e3, value, w0, w1, w2, w3]
  show List.foldl (fun acc (x : UInt8) => acc * 256 + x.toNat) 0 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] = _
  simp only [List.foldl_cons, List.foldl_nil, Nat.reducePow]
  omega

/-- `canon` is the remainder modulo P. -/
theorem canon_mod (u0 u1 u2 u3 : UInt64) : (Fe.canon u0 u1 u2 u3).toNat = value u0 u1 u2 u3 % P := by
  have lt := value_lt u0 u1 u2 u3
  rw [canon_spec]
  generalize value u0 u1 u2 u3 = v at *
  simp only [P, Nat.reducePow, Nat.reduceSub] at *
  by_cases big : v ≥ 115792089237316195423570985008687907853269984665640564039457584007908834671663
  · simp only [big, ↓reduceIte]
    rw [Nat.mod_eq_sub_mod big, Nat.mod_eq_of_lt (by omega)]
  · simp only [big, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- `reduceOnce` with no carry is the remainder modulo N. -/
theorem reduceOnce_mod (u0 u1 u2 u3 : UInt64) : (Sc.reduceOnce u0 u1 u2 u3 0).toNat = value u0 u1 u2 u3 % N := by
  have lt := value_lt u0 u1 u2 u3
  have h := reduceOnce_spec u0 u1 u2 u3 0 (by decide) (by
    rw [show (0 : UInt64).toNat = 0 from rfl]
    generalize value u0 u1 u2 u3 = v at *
    simp only [N, Nat.reducePow] at *
    omega)
  rw [h, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

/-- The field element thirty-two bytes stand for is the number they spell, modulo P. -/
theorem Fe.ofBytes_spec (b : ByteArray) (h : b.size = 32) : (Fe.ofBytes b).toNat = Secp.fromBE b % P := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32 b h
  rw [fromBE_words, Fe.ofBytes, canon_mod]

/-- The scalar thirty-two bytes stand for is the number they spell, modulo N. -/
theorem Sc.ofBytes_spec (b : ByteArray) (h : b.size = 32) : (Sc.ofBytes b).toNat = Secp.fromBE b % N := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32 b h
  rw [fromBE_words, Sc.ofBytes, reduceOnce_mod]

/-! ## Writing a number as bytes -/

/-- Two byte arrays with the same bytes in the same order are the same. -/
theorem bytes_ext (x y : ByteArray) (h : x.data.toList = y.data.toList) : x = y := by
  obtain ⟨⟨x⟩⟩ := x
  obtain ⟨⟨y⟩⟩ := y
  simp_all

/-- Four words written out byte by byte, most significant first, are the number written the way winnow
writes it. -/
theorem pushed_words (u0 u1 u2 u3 : UInt64) :
    pushWord (pushWord (pushWord (pushWord (ByteArray.emptyWithCapacity 32) u3) u2) u1) u0
      = Secp.toBE32 (value u0 u1 u2 u3) := by
  have b0 := u0.toNat_lt; have b1 := u1.toNat_lt; have b2 := u2.toNat_lt; have b3 := u3.toNat_lt
  apply bytes_ext
  simp [pushWord, ByteArray.push, Secp.toBE32, List.range, List.range.loop]
  rw [show (ByteArray.emptyWithCapacity 32).data.toList = [] from rfl, List.nil_append]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply UInt8.toNat_inj.mp
    simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, value,
      show (56 : UInt64).toNat = 56 from rfl, show (48 : UInt64).toNat = 48 from rfl,
      show (40 : UInt64).toNat = 40 from rfl, show (32 : UInt64).toNat = 32 from rfl,
      show (24 : UInt64).toNat = 24 from rfl, show (16 : UInt64).toNat = 16 from rfl,
      show (8 : UInt64).toNat = 8 from rfl, Nat.reducePow, Nat.reduceMod]
    omega

/-- A field element is written the way winnow writes its number. -/
theorem Fe.bytes_spec (a : Fe) : Fe.bytes a = Secp.toBE32 a.toNat := pushed_words a.a0 a.a1 a.a2 a.a3

/-- And so is a scalar. -/
theorem Sc.bytes_spec (a : Sc) : Sc.bytes a = Secp.toBE32 a.toNat := pushed_words a.a0 a.a1 a.a2 a.a3

end SecpCt
