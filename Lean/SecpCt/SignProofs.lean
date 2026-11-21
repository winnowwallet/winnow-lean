import Secp.Signing
import SecpCt.KeyProofs
import SecpCt.ScalarMulProofs

/-! # Signing

`signRaw_eq` and `sign_eq`: for thirty-two bytes that spell a number below N, whenever BIP 340's signing as
the reference writes it (`Secp.Bip340.signWith`, `Secp/Signing.lean`, over the specification's own `k·G`)
gives a signature, `signRaw` gives the same sixty-four bytes and `sign` returns them. The reference is the
BIP's steps on plain numbers and is not something that runs; `signRaw` is written to hide the key, and this
says it comes to the same bytes on every input.

It follows BIP 340's steps in order, and at each one the constant-time value is shown to be the reference's:
the public point, the key made even, the number the signature is made with, its point, that number made
even, the challenge, and the sum. The arithmetic is proved elsewhere (`SecpCt/ScalarProofs.lean`,
`SecpCt/ScalarMulProofs.lean`, `SecpCt/KeyProofs.lean`). What this file adds around it: a SHA-256 hash is
thirty-two bytes (`hash_size`), so that reading one as a scalar reads all of it, and the signer's xor of two
thirty-two byte strings is winnow's (`xor32_eq`).

Also here, because the signer calls them: `publicKey` returns the x of the secret times the generator and
whether its y is odd (`publicKey_spec`), and adding two keys gives their sum modulo N (`addRaw_spec`).

The one assumption is that of `SecpCt/CurveProofs.lean`: P is prime, as Fermat's little theorem for P.

One direction is not stated: that the reference gives a signature whenever `sign` does. Nothing relies on
it: whoever signs checks each signature with a verifier (`verify`, `SecpCt/Keys.lean`) before letting it out,
and what that accepting means is `verify_sound`. -/

namespace SecpCt
open Secp.Spec (F)
open Secp

/-- A SHA-256 hash is thirty-two bytes. -/
theorem hash_size (msg : ByteArray) : (Sha256.hash msg).size = 32 := by
  simp only [Sha256.hash]
  show (Sha256.State.toBytes _).size = 32
  have he : (ByteArray.emptyWithCapacity 32).size = 0 := rfl
  simp [Sha256.State.toBytes, Sha256.pushU32BE, ByteArray.size_push, he]

/-- And so is a tagged hash. -/
theorem tagged_size (tag : String) (msg : ByteArray) : (Sha256.tagged tag msg).size = 32 := hash_size _

theorem toList_loop (bs : ByteArray) : ∀ (n i : Nat) (r : List UInt8), i + n = bs.size →
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
    rfl

/-- The list of a byte array's bytes, as winnow takes it, is the list of its bytes. -/
theorem toList_bytes (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop bs bs.size 0 [] (by omega)]
  rfl

/-- The signer's xor of two thirty-two byte strings is winnow's. -/
theorem xor32_eq (a b : ByteArray) (ha : a.size = 32) (hb : b.size = 32) : xor32 a b = Secp.xorBytes a b := by
  simp only [xor32, ha, hb, and_self, ↓reduceDIte, Secp.xorBytes]
  apply bytes_ext
  apply List.ext_getElem
  · simp [toList_bytes, Array.length_toList, show a.data.size = a.size from rfl, show b.data.size = b.size from rfl, ha, hb]
  · intro i h1 h2
    rw [Array.getElem_toList, Array.getElem_ofFn]
    simp [toList_bytes, ByteArray.getElem_eq_getElem_data]
/-! ## The signature -/

/-- The number of points, here and in the specification. -/
theorem N_eq : N = Spec.N := by decide

/-- winnow writes a number as thirty-two bytes. -/
theorem toBE32_size (n : Nat) : (Secp.toBE32 n).size = 32 := by
  simp [Secp.toBE32, ByteArray.size]

/-- Nothing times a point is the point at infinity. -/
theorem smul_zero (p : Spec.Point) : Spec.smul 0 p = .inf := by
  unfold Spec.smul
  simp only [Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  generalize (List.range 256).reverse = l
  induction l with
  | nil => rfl
  | cons i l ih => exact ih

/-- The scalar, negated or not by the parity of a y coordinate, is the number the reference uses: `N − s` if
y is odd, `s` if not. -/
theorem negIf_parity (s : Sc) (hs : s.toNat < N) (y : Fe) (q : Nat) (hy : y.toNat = q) :
    (Sc.negIf y.isOdd s).toNat = (if q % 2 = 1 then Secp.negN s.toNat else s.toNat)
      ∧ (Sc.negIf y.isOdd s).toNat < N := by
  have parity := Fe.isOdd_spec y
  rw [hy] at parity
  by_cases odd : q % 2 = 1
  · have one : y.isOdd = 1 := by
      apply UInt64.toNat_inj.mp
      rw [parity, odd]
      rfl
    rw [one, Sc.negIf_one, Sc.neg_spec s hs]
    simp only [odd, ↓reduceIte, Secp.negN, N_eq]
    exact ⟨trivial, Nat.mod_lt _ (by decide)⟩
  · have zero : y.isOdd = 0 := by
      apply UInt64.toNat_inj.mp
      rw [parity]
      show q % 2 = 0
      omega
    rw [zero, Sc.negIf_zero]
    simp only [odd, ↓reduceIte]
    exact ⟨trivial, hs⟩

/-- When the specification's `k·G` gives two numbers, they are the coordinates of a point `k·G` is. -/
theorem mulG_point {k x y : Nat} (h : Spec.mulG k = some (x, y)) :
    ∃ px py : F, Spec.smul k Spec.G = .pt px py ∧ px.val = x ∧ py.val = y := by
  unfold Spec.mulG at h
  -- the product is named, never worked out: it is 256 doublings written out
  generalize Spec.smul k Spec.G = p at h
  cases p with
  | inf => simp only [reduceCtorEq] at h
  | pt px py =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨px, py, rfl, h.1, h.2⟩

/-- The two coordinates the code computes for a scalar are the numbers of the point the specification gives. -/
theorem affine_of_smul (s : Sc) (x y : Nat) (h : Spec.mulG s.toNat = some (x, y)) :
    (Point.mulGenerator s).affine.1.toNat = x ∧ (Point.mulGenerator s).affine.2.1.toNat = y := by
  obtain ⟨px, py, point, rfl, rfl⟩ := mulG_point h
  have rep := mulGenerator_rep s
  rw [point] at rep
  obtain ⟨hx, hy, _, vx, vy⟩ := affine_point rep
  exact ⟨Fe.toNat_of_toF vx hx, Fe.toNat_of_toF vy hy⟩

/-- **The signature is the reference's.** For thirty-two bytes that spell a number below N, whenever
winnow's reference signing gives a signature, `signRaw` gives the same bytes, and the bit beside them is the
one that says whether the secret is a key. -/
theorem signRaw_eq (secret m aux : ByteArray) (size : secret.size = 32)
    (below : Secp.fromBE secret < N) {sig pxb : ByteArray}
    (h : Secp.Bip340.signWith Spec.mulG m (Secp.fromBE secret) aux = some (sig, pxb)) :
    signRaw secret m aux = (sig, Sc.isKey secret) := by
  have keyBit : Sc.isKey secret = 0 ∨ Sc.isKey secret = 1 := by
    rw [Sc.isKey_spec secret size]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have secretNumber : (Sc.ofBytes secret).toNat = Secp.fromBE secret := by
    rw [Sc.ofBytes_spec secret size, Nat.mod_eq_of_lt below]
  generalize Secp.fromBE secret = d0 at *
  unfold Secp.Bip340.signWith at h
  by_cases ha : aux.size ≠ 32
  · simp [ha] at h
  simp only [ha, ite_false] at h
  cases hp : Spec.mulG d0 with
  | none => rw [hp] at h; cases h
  | some q =>
    obtain ⟨px, py⟩ := q
    rw [hp] at h
    simp only at h
    -- the public point, and the key made even
    obtain ⟨hpx, hpy⟩ := affine_of_smul (Sc.ofBytes secret) px py (by rw [secretNumber]; exact hp)
    obtain ⟨hd, dBelow⟩ := negIf_parity (Sc.ofBytes secret) (by rw [secretNumber]; exact below) _ py hpy
    rw [secretNumber] at hd
    -- the nonce
    generalize hk : hashMod _ = k0 at h
    by_cases hz : k0 = 0
    · simp [hz] at h
    simp only [hz, ite_false] at h
    cases hg : Spec.mulG k0 with
    | none => rw [hg] at h; cases h
    | some q =>
      rw [hg] at h
      cases q with
      | mk rx ry =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp only [signRaw]
        -- the key's bytes and the public key's bytes are the reference's
        have pxBytes : (Point.mulGenerator (Sc.ofBytes secret)).affine.1.bytes = toBE32 px := by
          rw [Fe.bytes_spec, hpx]
        have dBytes : (Sc.negIf (Point.mulGenerator (Sc.ofBytes secret)).affine.2.1.isOdd (Sc.ofBytes secret)).bytes
            = toBE32 (if py % 2 = 1 then negN d0 else d0) := by
          rw [Sc.bytes_spec, hd]
        simp only [pxBytes, dBytes]
        rw [xor32_eq _ _ (toBE32_size _) (tagged_size _ _)]
        generalize Sc.negIf (Point.mulGenerator (Sc.ofBytes secret)).affine.2.1.isOdd (Sc.ofBytes secret) = dd at *
        -- the number the signature is made with
        have nonce := Sc.ofBytes_spec _ (tagged_size "BIP0340/nonce"
          (xorBytes (toBE32 (if py % 2 = 1 then negN d0 else d0)) (Sha256.tagged "BIP0340/aux" aux)
            ++ toBE32 px ++ m))
        rw [N_eq] at nonce
        change _ = hashMod _ at nonce
        rw [hk] at nonce
        have k0Below : k0 < N := by
          rw [← hk, N_eq]
          exact Nat.mod_lt _ (by decide)
        generalize Sc.ofBytes (Sha256.tagged "BIP0340/nonce" _) = ks at *
        obtain ⟨hrx, hry⟩ := affine_of_smul ks rx ry (by rw [nonce]; exact hg)
        obtain ⟨hkk, kBelow⟩ := negIf_parity ks (by rw [nonce]; exact k0Below) _ ry hry
        rw [nonce] at hkk
        have rxBytes : (Point.mulGenerator ks).affine.1.bytes = toBE32 rx := by
          rw [Fe.bytes_spec, hrx]
        simp only [rxBytes]
        generalize Sc.negIf (Point.mulGenerator ks).affine.2.1.isOdd ks = kk at *
        -- the challenge
        have ch := Sc.ofBytes_spec _ (tagged_size "BIP0340/challenge" (toBE32 rx ++ toBE32 px ++ m))
        rw [N_eq] at ch
        change _ = challenge (toBE32 rx) (toBE32 px) m at ch
        generalize Sc.ofBytes (Sha256.tagged "BIP0340/challenge" _) = es at *
        -- and the sum
        rw [Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [Sc.bytes_spec, Sc.add_spec kk _ kBelow (Sc.mul_lt _ _), Sc.mul_spec, hkk, hd, ch, Nat.add_mod_mod, N_eq]
        · -- the number the signature is made with was not zero, so the bit is the key's
          rw [Sc.isZero_spec, nonce]
          simp only [hz, ↓reduceIte]
          rcases keyBit with e | e <;> rw [e] <;> rfl

/-- **`sign` returns the reference's signature.** For thirty-two bytes of secret that spell a number below N,
whenever winnow's reference signing gives a signature, `sign` returns that signature. -/
theorem sign_eq (secret m aux : ByteArray) (size : secret.size = 32)
    (below : Secp.fromBE secret < N) {sig pxb : ByteArray}
    (h : Secp.Bip340.signWith Spec.mulG m (Secp.fromBE secret) aux = some (sig, pxb)) :
    sign secret m aux = some sig := by
  have raw := signRaw_eq secret m aux size below h
  have auxSize : aux.size = 32 := by
    unfold Secp.Bip340.signWith at h
    by_cases ha : aux.size ≠ 32
    · simp [ha] at h
    · exact Decidable.not_not.mp ha
  have positive : 0 < Secp.fromBE secret := by
    apply Nat.pos_of_ne_zero
    intro zero
    have nothing : Spec.mulG 0 = none := by simp only [Spec.mulG, smul_zero]
    unfold Secp.Bip340.signWith at h
    simp [auxSize, zero, nothing] at h
  have key : Sc.isKey secret = 1 := by
    rw [Sc.isKey_spec secret size]
    simp only [positive, below, and_self, ↓reduceIte]
  simp only [sign, size, auxSize, raw, key]
  rfl

/-! ## The public key and adding keys, as the signer calls them -/

/-- The last of the thirty-two bytes winnow writes for a number says whether the number is odd. -/
theorem last_byte_parity (n : Nat) (h31 : 31 < (Secp.toBE32 n).size) :
    ((Secp.toBE32 n)[31]'h31).toUInt64 &&& 1 = if n % 2 = 1 then 1 else 0 := by
  have last : (Secp.toBE32 n)[31]'h31 = UInt8.ofNat n := by
    simp [Secp.toBE32, ByteArray.getElem_eq_getElem_data]
  rw [last]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt8.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl,
    Nat.and_one_is_mod]
  by_cases odd : n % 2 = 1
  · simp only [odd, ↓reduceIte]
    show n % 2 ^ 8 % 2 = 1
    omega
  · simp only [odd, ↓reduceIte]
    show n % 2 ^ 8 % 2 = 0
    omega

/-- **The public key.** For thirty-two bytes that spell a number `d` from 1 to N − 1, `publicKey` returns the
x of `d · G`, as winnow writes it, and whether its y is odd. -/
theorem publicKey_spec (secret : ByteArray) (size : secret.size = 32)
    (positive : 0 < Secp.fromBE secret) (below : Secp.fromBE secret < N) {x y : F}
    (point : Spec.smul (Secp.fromBE secret) Spec.G = .pt x y) :
    publicKey secret = some (Secp.toBE32 x.val, if y.val % 2 = 1 then 1 else 0) := by
  have raw := publicRaw_spec secret size (x := x) (y := y) (by rw [Nat.mod_eq_of_lt below]; exact point)
  have key : Sc.isKey secret = 1 := by
    rw [Sc.isKey_spec secret size]
    simp only [positive, below, and_self, ↓reduceIte]
  have hy : 31 < (Secp.toBE32 y.val).size := by rw [toBE32_size]; decide
  simp only [publicKey, size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, raw, key, beq_self_eq_true,
    hy, and_self, ↓reduceDIte, last_byte_parity]

/-- **Adding keys.** The sum `addRaw` returns is the sum of the two numbers modulo N, as winnow writes it, and
the bit beside it says whether that sum is not zero. -/
theorem addRaw_spec (a b : ByteArray) (ha : a.size = 32) (hb : b.size = 32) :
    addRaw a b = (Secp.toBE32 ((Secp.fromBE a + Secp.fromBE b) % N),
      if (Secp.fromBE a + Secp.fromBE b) % N = 0 then 0 else 1) := by
  have la : (Sc.ofBytes a).toNat < N := by
    rw [Sc.ofBytes_spec a ha]; exact Nat.mod_lt _ (by decide)
  have lb : (Sc.ofBytes b).toNat < N := by
    rw [Sc.ofBytes_spec b hb]; exact Nat.mod_lt _ (by decide)
  have sum : (Sc.add (Sc.ofBytes a) (Sc.ofBytes b)).toNat = (Secp.fromBE a + Secp.fromBE b) % N := by
    rw [Sc.add_spec _ _ la lb, Sc.ofBytes_spec a ha, Sc.ofBytes_spec b hb, ← Nat.add_mod]
  simp only [addRaw, Sc.bytes_spec, Sc.isZero_spec, sum]
  split <;> rfl

end SecpCt
