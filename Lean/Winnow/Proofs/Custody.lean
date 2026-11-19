import Lean.Elab.Term
import SecpCt.CompleteProofs
import Winnow.Spec.Custody
import Winnow.Tx.Taproot

/-! # The key behind every address the wallet shows can sign for it (#125, phase 2)

A wallet derives an address twice: from public keys, to show it and watch it, and from private keys, to
sign for what was paid to it. If the two ever disagree the coins paid there are lost, and no test can try
every index and every tweak. These theorems say they agree, for every key and every index:

1. **Tweaking a public key is tweaking the secret key** (`publicAdd_eq_privateAdd`,
   `xonlyAdd_eq_keypairXonlyAdd`): the same point, or the same refusal, for any bytes given as the tweak.
2. **BIP 32** (`HDKey.child_neutered_comm`, `HDKey.child2_neutered_comm`,
   `HDKey.child_preserves_wellFormed`): at an index that is not hardened, the child of the watch-only key is
   the watch-only form of the child of the private key.
3. **Taproot and BIP 86** (`Taproot.keyPath_spendable`, `BIP86.tweakedPrivateKey_spendable`): whenever the
   watch-only derivation gives a script, the private derivation gives the key that signs for it.
4. **Script trees** (`Taproot.branchHash_comm`, `Taproot.hashes_reconstruct`, `Taproot.controlBlocks_valid`):
   every control block the wallet makes commits its leaf into the output it is for.
5. **A card for one person** (`SilentPaymentPairing.codeSpendSecret_spendable`, `codeFor_spendable`,
   `issue_spendable`): the secret the wallet derives for a payment signs for the script the payer derives.

"Signs for" is `Winnow.Spec.Custody.KeyPathSpendable`: the wallet's own BIP 340 signatures with the key
verify, by the wallet's own check, under the key in the script. Bitcoin Core's verifier is not in these
proofs; the regtest suites hold the two together.

**How these proofs are written, and why.** Lean's kernel will unfold anything. Left comparing two terms that
branch on `pointOfSecret d`, it evaluates `pointOfSecret d`: a 256-step ladder over a number it does not
know, which does not end. So nothing here ever makes the kernel look inside the curve code:

- the curve and hash functions are marked irreducible for this file, which keeps the elaborator out;
- a step inside a function is rewritten by a closed equation (`rw [h]`), never simplified in place while the
  thing branched on is still a curve call;
- a function with several such steps is reasoned about through `body%`, with its callees as variables. -/

namespace Winnow.Proofs.Custody

open Secp
open Winnow.Keys
open Winnow.Spec.Custody

open Lean Elab Term Meta in
/-- `body% f [c₁, …] [x₁, …]`: the definition of `f` with each constant `cᵢ` replaced by the term `xᵢ`; with
no constants, `f`'s definition itself.

A proof tool, in no statement that is kept. The kernel has no notion of "do not unfold": when a proof step
leaves it comparing two `match`es on `pointOfSecret d`, it evaluates `pointOfSecret d`, a 256-step ladder on a
symbolic number, and does not come back. So a function that calls the curve is reasoned about in two steps:
a lemma about `body% f [pointOfSecret, …] [pos, …]`, where the callees are variables and any simplification is
cheap to check, and then `rw [f_def]; exact lemma …`, which the kernel checks by seeing that the two terms are
the same term. -/
elab "body% " f:ident "[" cs:ident,* "]" "[" xs:term,* "]" : term => do
  let fn ← realizeGlobalConstNoOverload f
  let info ← getConstInfo fn
  let cns ← cs.getElems.mapM (realizeGlobalConstNoOverload ·)
  let xes ← xs.getElems.mapM (elabTerm · none)
  return info.value!.replace fun e => match e with
    | .const n _ => (cns.idxOf? n).map (xes[·]!)
    | _ => none

/-! The curve code and the hashes are never unfolded by these proofs: everything said about them comes from
the theorems of `SecpCt` and from their being functions. Marking them irreducible here keeps the elaborator
(and so the terms the kernel checks) from trying, which with 256-step loops inside does not end. -/
attribute [local irreducible] SecpCt.Sc.bytes SecpCt.Sc.ofBytes SecpCt.Sc.isKey SecpCt.Sc.add SecpCt.Sc.neg
  SecpCt.Sc.mul SecpCt.Sc.isZero SecpCt.publicPoint SecpCt.scalar? SecpCt.evenKey SecpCt.pointAdd
  SecpCt.pointMul SecpCt.generatorMul SecpCt.combine SecpCt.liftX? SecpCt.parseXOnly SecpCt.parseCompressed
  SecpCt.parseUncompressed SecpCt.sign SecpCt.verify SecpCt.signVerified SecpCt.publicKey
  Secp.fromBE Secp.toBE32 Secp.xorBytes Secp.hashMod Secp.Sha256.hash Secp.Sha256.tagged
  Winnow.sha256 Winnow.taggedHash Winnow.hmacSha512

/-! ## 1. 32-byte big-endian round-trip & strict lexicographic order on `ByteArray` -/

private def foldBE (acc : Nat) (x : UInt8) : Nat := acc * 256 + x.toNat

private theorem foldBE_shift (l : List UInt8) (acc : Nat) :
    l.foldl foldBE acc = acc * 2 ^ (8 * l.length) + l.foldl foldBE 0 ∧
    l.foldl foldBE 0 < 2 ^ (8 * l.length) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨h1, hlt⟩ := ih (foldBE acc x)
    obtain ⟨h0, _⟩ := ih (foldBE 0 x)
    have hx := x.toNat_lt
    have hpow : 2 ^ (8 * (xs.length + 1)) = 256 * 2 ^ (8 * xs.length) := by
      rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length by omega, Nat.pow_add]
    rw [h1, h0, hpow]
    simp only [foldBE, Nat.zero_mul, Nat.zero_add]
    have hdist : (acc * 256 + x.toNat) * 2 ^ (8 * xs.length) =
        acc * (256 * 2 ^ (8 * xs.length)) + x.toNat * 2 ^ (8 * xs.length) := by grind
    have hbound : x.toNat * 2 ^ (8 * xs.length) + xs.foldl foldBE 0 < 256 * 2 ^ (8 * xs.length) := by
      have hle : (x.toNat + 1) * 2 ^ (8 * xs.length) ≤ 256 * 2 ^ (8 * xs.length) :=
        Nat.mul_le_mul_right _ hx
      have hadd : (x.toNat + 1) * 2 ^ (8 * xs.length) = x.toNat * 2 ^ (8 * xs.length) + 2 ^ (8 * xs.length) :=
        Nat.succ_mul x.toNat _
      omega
    exact ⟨by omega, hbound⟩

private theorem foldBE_getElem (l : List UInt8) (i : Nat) (hi : i < l.length) :
    UInt8.ofNat (l.foldl foldBE 0 / 2 ^ (8 * (l.length - 1 - i))) = l[i] := by
  have hsplit : l = l.take i ++ (l[i] :: l.drop (i + 1)) := by
    rw [List.getElem_cons_drop hi, List.take_append_drop]
  have hval := congrArg (List.foldl foldBE 0) hsplit
  rw [List.foldl_append, List.foldl_cons] at hval
  obtain ⟨hshift, hrem_lt⟩ := foldBE_shift (l.drop (i + 1)) (foldBE (List.foldl foldBE 0 (l.take i)) l[i])
  have hlen_drop : (l.drop (i + 1)).length = l.length - 1 - i := by rw [List.length_drop]; omega
  rw [hlen_drop] at hshift hrem_lt
  rw [hshift] at hval
  have hp_pos : 0 < 2 ^ (8 * (l.length - 1 - i)) := Nat.two_pow_pos _
  have hdiv : l.foldl foldBE 0 / 2 ^ (8 * (l.length - 1 - i)) =
      foldBE (List.foldl foldBE 0 (l.take i)) l[i] := by
    rw [hval, Nat.mul_comm _ (2 ^ _), Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hrem_lt, Nat.add_zero]
  rw [hdiv]
  apply UInt8.toNat_inj.mp
  have hx := l[i].toNat_lt
  simp only [UInt8.toNat_ofNat', foldBE, Nat.reducePow]
  omega

theorem toBE32_fromBE {b : ByteArray} (h : b.size = 32) : Secp.toBE32 (Secp.fromBE b) = b := by
  have hlen : b.data.toList.length = 32 := by rw [Array.length_toList]; exact h
  have hfb : Secp.fromBE b = b.data.toList.foldl foldBE 0 := by
    unfold Secp.fromBE; exact SecpCt.foldl_bytes foldBE 0 b
  apply SecpCt.bytes_ext
  apply List.ext_getElem
  · show (Secp.toBE32 (Secp.fromBE b)).size = b.size
    rw [SecpCt.toBE32_size, h]
  · intro i h1 h2
    have hi32 : i < 32 := hlen ▸ h2
    have hget : (Secp.toBE32 (Secp.fromBE b)).data.toList[i]'h1 =
        UInt8.ofNat (Secp.fromBE b / 2 ^ (8 * (31 - i))) := by
      simp [Secp.toBE32]
    rw [hget, hfb, show 31 - i = b.data.toList.length - 1 - i by omega, foldBE_getElem b.data.toList i h2]

private theorem lexLt_go_asymm (a b : ByteArray) :
    ∀ (fuel i : Nat), ByteArray.lexLt.go a b i fuel = true → ByteArray.lexLt.go b a i fuel = false
  | 0, _ => by
    simp only [ByteArray.lexLt.go, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  | fuel + 1, i => by
    simp only [ByteArray.lexLt.go]
    by_cases hab : i < a.size ∧ i < b.size
    · have hba : i < b.size ∧ i < a.size := ⟨hab.2, hab.1⟩
      simp only [hab]
      by_cases hlt : a[i]'hab.1 < b[i]'hab.2
      · have hgt : ¬ (b[i]'hab.2 < a[i]'hab.1) := by simp [UInt8.lt_iff_toNat_lt] at hlt ⊢; omega
        simp [hlt, hgt]
      · by_cases hgt : b[i]'hab.2 < a[i]'hab.1
        · simp [hlt, hgt]
        · simp only [hlt, hgt, ↓reduceIte]
          exact lexLt_go_asymm a b fuel (i + 1)
    · have hba : ¬ (i < b.size ∧ i < a.size) := fun h => hab ⟨h.2, h.1⟩
      simp only [hab, hba, ↓reduceDIte, decide_eq_true_eq, decide_eq_false_iff_not]
      omega

private theorem eq_of_lexLt_go_false (a b : ByteArray) :
    ∀ (fuel i : Nat),
      i + fuel = min a.size b.size →
      ByteArray.lexLt.go a b i fuel = false →
      ByteArray.lexLt.go b a i fuel = false →
      (∀ j, j < i → (hj1 : j < a.size) → (hj2 : j < b.size) → a[j]'hj1 = b[j]'hj2) →
      a = b
  | 0, i, hfuel, h1, h2, hpre => by
    simp only [ByteArray.lexLt.go, decide_eq_false_iff_not] at h1 h2
    have hsz : a.size = b.size := by omega
    have hi_eq : i = a.size := by omega
    apply SecpCt.bytes_ext
    apply List.ext_getElem
    · exact hsz
    · intro j hj1 hj2
      have hja : j < a.size := hj1
      have hjb : j < b.size := hj2
      rw [Array.getElem_toList, Array.getElem_toList,
          ← ByteArray.getElem_eq_getElem_data, ← ByteArray.getElem_eq_getElem_data]
      exact hpre j (by omega) hja hjb
  | fuel + 1, i, hfuel, h1, h2, hpre => by
    have hab : i < a.size ∧ i < b.size := ⟨by omega, by omega⟩
    have hba : i < b.size ∧ i < a.size := ⟨hab.2, hab.1⟩
    simp only [ByteArray.lexLt.go, hab] at h1 h2
    by_cases hlt : a[i]'hab.1 < b[i]'hab.2
    · simp [hlt] at h1
    · by_cases hgt : b[i]'hab.2 < a[i]'hab.1
      · simp [hgt] at h2
      · simp only [hlt, hgt, ↓reduceIte] at h1 h2
        have heq_i : a[i]'hab.1 = b[i]'hab.2 := by
          apply UInt8.toNat_inj.mp
          simp [UInt8.lt_iff_toNat_lt] at hlt hgt
          omega
        apply eq_of_lexLt_go_false a b fuel (i + 1) (by omega) h1 h2
        intro j hj hj1 hj2
        by_cases hji : j = i
        · subst hji; exact heq_i
        · exact hpre j (by omega) hj1 hj2

theorem lexLt_asymm {a b : ByteArray} (h : ByteArray.lexLt a b = true) :
    ByteArray.lexLt b a = false := by
  unfold ByteArray.lexLt at h ⊢
  rw [Nat.min_comm b.size a.size]
  exact lexLt_go_asymm a b (min a.size b.size) 0 h

theorem eq_of_not_lexLt {a b : ByteArray}
    (h1 : ByteArray.lexLt a b = false) (h2 : ByteArray.lexLt b a = false) : a = b := by
  unfold ByteArray.lexLt at h1 h2
  rw [Nat.min_comm b.size a.size] at h2
  exact eq_of_lexLt_go_false a b (min a.size b.size) 0 (Nat.zero_add _) h1 h2
    (fun _ hj => absurd hj (Nat.not_lt_zero _))

theorem Taproot.branchHash_comm (a b : ByteArray) :
    Taproot.branchHash a b = Taproot.branchHash b a := by
  unfold Taproot.branchHash lexPrecedes
  cases hab : ByteArray.lexLt a b
  · cases hba : ByteArray.lexLt b a
    · rw [eq_of_not_lexLt hab hba]
    · simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [lexLt_asymm hab]
    simp only [Bool.false_eq_true, ↓reduceIte]

/-! ## 2. `Winnow.Keys.Secret` invariants & tweak commutativity -/

/-- A secret key is a number from 1 to N − 1. Every `Secret` the wallet makes is one (its constructor is
private to `Winnow/Keys/Secp256k1.lean`, whose functions check it); the theorems take it as a hypothesis, and
`secretOf_valid`, `privateAdd_valid` and `keypairXonlyAdd_valid` discharge it for the keys those return. -/
def _root_.Winnow.Keys.Secret.Valid (d : Secret) : Prop :=
  0 < d.scalar.toNat ∧ d.scalar.toNat < SecpCt.N

private theorem throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl
private theorem pure_eq {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
private theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
private theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl
private theorem found_some {α : Type} (a : α) : found (some a) = .ok a := rfl
private theorem found_none {α : Type} : found (none : Option α) = .error .underlyingCryptoError := rfl
private theorem found_ok {α : Type} {o : Option α} {a : α} (h : found o = .ok a) : o = some a := by
  cases o with
  | none => rw [found_none] at h; cases h
  | some b => rw [found_some] at h; injection h with h; rw [h]

private theorem Sc.neg_neg {x : SecpCt.Sc} (hx : x.toNat < SecpCt.N) :
    SecpCt.Sc.neg (SecpCt.Sc.neg x) = x := by
  apply SecpCt.Sc.toNat_inj
  have hn1 : (SecpCt.Sc.neg x).toNat < SecpCt.N := by
    rw [SecpCt.Sc.neg_spec x hx]; exact Nat.mod_lt _ (by decide)
  rw [SecpCt.Sc.neg_spec _ hn1, SecpCt.Sc.neg_spec x hx]
  by_cases hx0 : x.toNat = 0
  · simp [hx0]
  · have hsub1 : (SecpCt.N - x.toNat) % SecpCt.N = SecpCt.N - x.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hsub1, show SecpCt.N - (SecpCt.N - x.toNat) = x.toNat by omega, Nat.mod_eq_of_lt hx]

private theorem privateNegate_involutive {d : Secret} (hd : d.scalar.toNat < SecpCt.N) :
    privateNegate (privateNegate d) = d := by
  unfold privateNegate
  dsimp only
  rw [Sc.neg_neg hd]

theorem Secret.ext_below {a b : Secret}
    (ha : a.scalar.toNat < SecpCt.N) (hb : b.scalar.toNat < SecpCt.N) (h : a.scalar = b.scalar) :
    a = b := by
  have hneg : privateNegate a = privateNegate b := by unfold privateNegate; rw [h]
  rw [← privateNegate_involutive ha, ← privateNegate_involutive hb, hneg]

theorem isValidSecret_iff (b : ByteArray) :
    isValidSecret b = true ↔ b.size = 32 ∧ 0 < Secp.fromBE b ∧ Secp.fromBE b < SecpCt.N := by
  unfold isValidSecret
  by_cases hsz : b.size = 32
  · rw [SecpCt.Sc.isKey_spec b hsz]
    simp only [hsz, beq_self_eq_true, Bool.true_and, true_and]
    split <;> simp_all
  · simp [hsz]

theorem secretOf_valid {b : ByteArray} {d : Secret} (h : secretOf b = .ok d) :
    d.Valid ∧ d.bytes = b ∧ b.size = 32 ∧ d.scalar.toNat = Secp.fromBE b := by
  unfold secretOf at h
  by_cases hsz : b.size = 32
  · simp only [hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hk : SecpCt.Sc.isKey b == 1
    · simp only [hk, ↓reduceIte] at h
      injection h with hd
      have hsc : d.scalar = SecpCt.Sc.ofBytes b := congrArg Secret.scalar hd.symm
      simp only [beq_iff_eq] at hk
      rw [SecpCt.Sc.isKey_spec b hsz] at hk
      have hrange : 0 < Secp.fromBE b ∧ Secp.fromBE b < SecpCt.N := by
        split at hk
        · assumption
        · exact absurd hk (by decide)
      have hnat : d.scalar.toNat = Secp.fromBE b := by
        rw [hsc, SecpCt.Sc.ofBytes_spec b hsz, Nat.mod_eq_of_lt hrange.2]
      have hbytes : d.bytes = b := by
        unfold Secret.bytes
        rw [SecpCt.Sc.bytes_spec, hnat, toBE32_fromBE hsz]
      exact ⟨⟨hnat ▸ hrange.1, hnat ▸ hrange.2⟩, hbytes, hsz, hnat⟩
    · simp [hk, throw_eq] at h
  · have hne : (b.size != 32) = true := bne_iff_ne.mpr hsz
    simp [hne, throw_eq] at h

theorem secretOf_of_isValidSecret {b : ByteArray} (h : isValidSecret b = true) :
    ∃ d, secretOf b = .ok d ∧ d.Valid ∧ d.bytes = b := by
  obtain ⟨hsz, hpos, hlt⟩ := (isValidSecret_iff b).mp h
  have hk : SecpCt.Sc.isKey b = 1 := by
    rw [SecpCt.Sc.isKey_spec b hsz]; simp [hpos, hlt]
  have hs : ∃ d, secretOf b = .ok d := by
    unfold secretOf
    simp [hsz, hk, pure, Except.pure]
  obtain ⟨d, hd⟩ := hs
  obtain ⟨hval, hbytes, _, _⟩ := secretOf_valid hd
  exact ⟨d, hd, hval, hbytes⟩

theorem secretOf_bytes {d : Secret} (hd : d.Valid) : secretOf d.bytes = .ok d := by
  have hsz : d.bytes.size = 32 := SecpCt.Sc.bytes_size d.scalar
  have hfb : Secp.fromBE d.bytes = d.scalar.toNat := SecpCt.Sc.fromBE_bytes d.scalar
  have hvis : isValidSecret d.bytes = true := (isValidSecret_iff d.bytes).mpr
    ⟨hsz, by rw [hfb]; exact hd.1, by rw [hfb]; exact hd.2⟩
  obtain ⟨d', hd', hval', _⟩ := secretOf_of_isValidSecret hvis
  obtain ⟨_, _, _, hnat'⟩ := secretOf_valid hd'
  have heq : d' = d := Secret.ext_below hval'.2 hd.2 (SecpCt.Sc.toNat_inj (hnat'.trans hfb))
  rw [heq] at hd'
  exact hd'

theorem pointOfSecret_complete {d : Secret} (hd : d.Valid) :
    ∃ p : Point, pointOfSecret d = .ok p ∧ p.Good ∧ p.spec = Spec.smul d.scalar.toNat Spec.G := by
  obtain ⟨p, hp, hspec, hgood⟩ := SecpCt.publicPoint_complete hd.1 hd.2
  refine ⟨p, ?_, hgood, hspec⟩
  show found (SecpCt.publicPoint d.scalar) = .ok p
  rw [hp]; rfl

theorem pointOfSecret_spec {d : Secret} {p : Point} (hp : pointOfSecret d = .ok p) :
    p.Good ∧ p.spec = Spec.smul d.scalar.toNat Spec.G := by
  unfold pointOfSecret at hp
  obtain ⟨hspec, hgood⟩ := SecpCt.publicPoint_spec (found_ok hp)
  exact ⟨hgood, hspec.symm⟩

private theorem nsmul_G_eq_inf_iff {k : Nat} (hk : k < 2 * Spec.N) :
    Spec.nsmul k Spec.G = .inf ↔ k = 0 ∨ k = Spec.N := by
  constructor
  · intro h
    rw [SecpCt.nsmul_mod_N] at h
    by_cases hmod : k % Spec.N = 0
    · by_cases hkN : k < Spec.N
      · left; rwa [Nat.mod_eq_of_lt hkN] at hmod
      · right
        have h2 : (k - Spec.N) % Spec.N = 0 := by
          rw [← Nat.mod_eq_sub_mod (Nat.le_of_not_lt hkN)]; exact hmod
        rw [Nat.mod_eq_of_lt (by omega)] at h2
        omega
    · have hlt : k % Spec.N < Spec.N := Nat.mod_lt _ (by decide)
      rw [← Spec.smul_eq_nsmul (k % Spec.N) (Nat.lt_trans hlt (by decide)) Spec.G_onCurve] at h
      exact absurd h (SecpCt.smul_G_ne_inf (Nat.pos_of_ne_zero hmod) hlt)
  · rintro (rfl | rfl)
    · rfl
    · rw [← Spec.smul_eq_nsmul Spec.N (by decide) Spec.G_onCurve]
      exact SecpCt.smul_N_G

/-- A tweak that is read is 32 bytes spelling a number below N. -/
theorem tweak32_ok {tw : ByteArray} {t : SecpCt.Sc} (h : tweak32 tw = .ok t) :
    tw.size = 32 ∧ t.toNat = Secp.fromBE tw ∧ t.toNat < SecpCt.N := by
  unfold tweak32 at h
  split at h
  · rw [throw_eq] at h; cases h
  · obtain ⟨hsz, hnat, hb⟩ := SecpCt.scalar?_spec (found_ok h)
    exact ⟨hsz, hnat, by rw [hnat]; exact hb⟩

private theorem isZero_iff (s : SecpCt.Sc) : (s.isZero == 1) = true ↔ s.toNat = 0 := by
  rw [SecpCt.Sc.isZero_spec]
  by_cases h0 : s.toNat = 0
  · simp [h0]
  · simp [h0]

/-- A key that `privateAdd` returns is a key, and its number is the sum modulo N. -/
theorem privateAdd_valid {d d' : Secret} {tw : ByteArray}
    (hd : d.Valid) (h : privateAdd d tw = .ok d') :
    d'.Valid ∧ ∃ t : SecpCt.Sc, tweak32 tw = .ok t ∧ t.toNat < SecpCt.N ∧
      d'.scalar = SecpCt.Sc.add d.scalar t := by
  unfold privateAdd at h
  cases htw : tweak32 tw with
  | error e => rw [htw, error_bind] at h; cases h
  | ok t =>
    rw [htw, ok_bind] at h
    obtain ⟨_, _, ht_lt⟩ := tweak32_ok htw
    simp +zetaHave only [] at h
    split at h
    · rw [throw_eq] at h; cases h
    · rename_i hz
      rw [pure_eq] at h; injection h with h; subst h
      have hs_lt := SecpCt.Sc.add_lt d.scalar t hd.2 ht_lt
      have hs_pos : 0 < (SecpCt.Sc.add d.scalar t).toNat :=
        Nat.pos_of_ne_zero fun h0 => hz ((isZero_iff _).mpr h0)
      exact ⟨⟨hs_pos, hs_lt⟩, t, rfl, ht_lt, rfl⟩

/-- **Tweaking the public key is tweaking the secret key.** For a key `d` with public point `p = d·G` and
*any* bytes `tw` (a tweak, the wrong size, a number of N or more, or one that brings the sum to zero),
`publicAdd p tw` is exactly what `privateAdd d tw` gives, taken to its public point: the same point, or the
same refusal. BIP 32's public derivation and BIP 341's output key are this. -/
theorem publicAdd_eq_privateAdd {d : Secret} {p : Point}
    (hd : d.Valid) (hp : pointOfSecret d = .ok p) (tw : ByteArray) :
    publicAdd p tw = (privateAdd d tw >>= pointOfSecret) := by
  obtain ⟨hpgood, hpspec⟩ := pointOfSecret_spec hp
  unfold publicAdd privateAdd
  cases htw : tweak32 tw with
  | error e => rfl
  | ok t =>
    rw [ok_bind, ok_bind]
    obtain ⟨_, _, ht_lt⟩ := tweak32_ok htw
    have hlt256 : SecpCt.N < 2 ^ 256 := by decide
    have hsum_spec : Spec.add (Spec.smul t.toNat Spec.G) p.spec =
        Spec.nsmul (d.scalar.toNat + t.toNat) Spec.G := by
      rw [hpspec,
          Spec.smul_eq_nsmul t.toNat (Nat.lt_trans ht_lt hlt256) Spec.G_onCurve,
          Spec.smul_eq_nsmul d.scalar.toNat (Nat.lt_trans hd.2 hlt256) Spec.G_onCurve,
          Spec.add_comm, ← Spec.nsmul_add d.scalar.toNat t.toNat Spec.G_onCurve]
    have hs_nat : (SecpCt.Sc.add d.scalar t).toNat = (d.scalar.toNat + t.toNat) % SecpCt.N :=
      SecpCt.Sc.add_spec d.scalar t hd.2 ht_lt
    simp +zetaHave only []
    generalize SecpCt.Sc.add d.scalar t = s at hs_nat ⊢
    have hs_lt : s.toNat < SecpCt.N := by rw [hs_nat]; exact Nat.mod_lt _ (by decide)
    have hmod : Spec.nsmul (d.scalar.toNat + t.toNat) Spec.G = Spec.nsmul s.toNat Spec.G := by
      rw [SecpCt.nsmul_mod_N, ← SecpCt.N_eq, ← hs_nat]
    rw [hmod] at hsum_spec
    by_cases hz : (s.isZero == 1) = true
    · -- the sum is zero modulo N: both sides refuse
      simp only [hz, ↓reduceIte]
      rw [throw_eq, error_bind]
      have hs0 : s.toNat = 0 := (isZero_iff s).mp hz
      rw [hs0] at hsum_spec
      cases hto : SecpCt.pointAdd p t with
      | none => rfl
      | some q =>
        obtain ⟨hq, _⟩ := SecpCt.pointAdd_spec hpgood hto
        rw [hsum_spec] at hq
        cases hq
    · -- the sum is from 1 to N − 1: both sides give its public point
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      rw [pure_eq, ok_bind]
      have hs_pos : 0 < s.toNat := Nat.pos_of_ne_zero fun h0 => hz ((isZero_iff s).mpr h0)
      obtain ⟨p', hp', hp'_spec, hp'_good⟩ := SecpCt.publicPoint_complete hs_pos hs_lt
      rw [← Spec.smul_eq_nsmul s.toNat (Nat.lt_trans hs_lt hlt256) Spec.G_onCurve, ← hp'_spec] at hsum_spec
      have hrep : SecpCt.Rep (SecpCt.Point.add (SecpCt.Point.mulPublic t SecpCt.Point.generator) p.point)
          p'.spec := by
        rw [← hsum_spec]
        exact SecpCt.rep_add (Spec.smul_onCurve t.toNat Spec.G_onCurve) hpgood.2.2
          (SecpCt.mulPublic_rep t Spec.G_onCurve SecpCt.rep_generator) (SecpCt.Affine.rep hpgood)
      obtain ⟨q, hto, hq_spec, hq_good⟩ := SecpCt.toAffine?_complete hp'_good.2.2 hrep
      have hqp' : q = p' := SecpCt.Affine.ext_spec hq_good hp'_good hq_spec
      have hpa : SecpCt.pointAdd p t = some p' := by
        unfold SecpCt.pointAdd; rw [hto, hqp']
      show found (SecpCt.pointAdd p t) = found (SecpCt.publicPoint s)
      rw [hpa, hp']

/-- The even-y partner of a key is a key. -/
theorem evenKey_valid {d : Secret} (hd : d.Valid) :
    0 < (SecpCt.evenKey d.scalar).toNat ∧ (SecpCt.evenKey d.scalar).toNat < SecpCt.N := by
  obtain ⟨p, hp, hpgood, hpspec⟩ := pointOfSecret_complete hd
  rw [SecpCt.evenKey_spec d.scalar hd.2 (x := p.x.toF) (y := p.y.toF) hpspec.symm]
  have h1 := hd.1
  have h2 := hd.2
  split
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · exact hd

/-- A key that `keypairXonlyAdd` returns is a key. -/
theorem keypairXonlyAdd_valid {d d' : Secret} {tw : ByteArray}
    (hd : d.Valid) (h : keypairXonlyAdd d tw = .ok d') :
    d'.Valid := by
  have hev_valid := evenKey_valid hd
  unfold keypairXonlyAdd at h
  cases htw : tweak32 tw with
  | error e => rw [htw, error_bind] at h; cases h
  | ok t =>
    rw [htw, ok_bind] at h
    obtain ⟨_, _, ht_lt⟩ := tweak32_ok htw
    simp +zetaHave only [] at h
    split at h
    · rw [throw_eq] at h; cases h
    · rename_i hz
      rw [pure_eq] at h; injection h with h; subst h
      exact ⟨Nat.pos_of_ne_zero fun h0 => hz ((isZero_iff _).mpr h0),
        SecpCt.Sc.add_lt _ t hev_valid.2 ht_lt⟩

private theorem isOdd_iff (p : Point) : p.isOdd = true ↔ p.y.toNat % 2 = 1 := by
  have parity := SecpCt.Fe.isOdd_spec p.y
  unfold SecpCt.Affine.isOdd
  rw [beq_iff_eq]
  constructor
  · intro h
    rw [h] at parity
    exact parity.symm
  · intro h
    apply UInt64.toNat_inj.mp
    rw [parity, h]
    rfl

private theorem neg_spec {p : Point} (hp : p.Good) : p.neg.spec = Spec.neg p.spec := by
  unfold SecpCt.Affine.neg SecpCt.Affine.spec Spec.neg
  simp only [SecpCt.toF_neg _ hp.2.1]

/-- The point with the same x and an even y: what an x-only key stands for (BIP 340). -/
def evenPoint (p : Point) : Point := if p.isOdd then p.neg else p

/-- **The even-y partner's public point.** For a key `d` with public point `p`, the public point of
`evenKey d` is `p` if its y is even and `−p` if it is odd. -/
theorem evenKey_point {d : Secret} {p : Point} (hd : d.Valid) (hp : pointOfSecret d = .ok p) :
    SecpCt.publicPoint (SecpCt.evenKey d.scalar) = some (evenPoint p) := by
  obtain ⟨hpgood, hpspec⟩ := pointOfSecret_spec hp
  obtain ⟨hev_pos, hev_lt⟩ := evenKey_valid hd
  obtain ⟨hev_good, _, _, _⟩ := SecpCt.Affine.evenPartner_good hpgood
  have hev_nat := SecpCt.evenKey_spec d.scalar hd.2 (x := p.x.toF) (y := p.y.toF) hpspec.symm
  have hy_val : p.y.toF.val = p.y.toNat := Nat.mod_eq_of_lt hpgood.2.1
  rw [hy_val] at hev_nat
  have h1 := hd.1
  have h2 := hd.2
  obtain ⟨q, hq, hq_spec, hq_good⟩ := SecpCt.publicPoint_complete hev_pos hev_lt
  rw [hq]
  congr 1
  apply SecpCt.Affine.ext_spec hq_good hev_good
  rw [hq_spec, hev_nat]
  by_cases hodd : p.y.toNat % 2 = 1
  · have hisOdd : p.isOdd = true := (isOdd_iff p).mpr hodd
    simp only [hodd, ↓reduceIte, hisOdd]
    rw [Nat.mod_eq_of_lt (by omega), SecpCt.N_eq,
      SecpCt.smul_neg_G h1 (by rw [← SecpCt.N_eq]; exact h2), ← hpspec, neg_spec hpgood]
  · have hisOdd : p.isOdd = false := by
      cases h : p.isOdd with
      | false => rfl
      | true => exact absurd ((isOdd_iff p).mp h) hodd
    simp only [hodd, ↓reduceIte, hisOdd, Bool.false_eq_true]
    exact hpspec.symm

/-- The even-y partner of a key, as a key: the key `keypairXonlyAdd` adds its tweak to. -/
theorem evenSecret_exists {d : Secret} (hd : d.Valid) :
    ∃ de : Secret, de.Valid ∧ de.scalar = SecpCt.evenKey d.scalar := by
  obtain ⟨hev_pos, hev_lt⟩ := evenKey_valid hd
  have hvis : isValidSecret (SecpCt.evenKey d.scalar).bytes = true := by
    rw [isValidSecret_iff]
    exact ⟨SecpCt.Sc.bytes_size _, by rw [SecpCt.Sc.fromBE_bytes]; exact hev_pos,
           by rw [SecpCt.Sc.fromBE_bytes]; exact hev_lt⟩
  obtain ⟨de, hde, hde_val, _⟩ := secretOf_of_isValidSecret hvis
  obtain ⟨_, _, _, hde_nat⟩ := secretOf_valid hde
  exact ⟨de, hde_val, SecpCt.Sc.toNat_inj (hde_nat.trans (SecpCt.Sc.fromBE_bytes _))⟩

/-- An x-only key that was written from a point reads back as that point's even-y partner. -/
theorem parseXonly_xonlyBytes {p : Point} (hp : p.Good) : parseXonly (xonlyBytes p) = .ok (evenPoint p) := by
  have hxsz : (xonlyBytes p).size = 32 := SecpCt.Fe.bytes_size p.x
  have hx_ext : (xonlyBytes p).extract 0 32 = xonlyBytes p := by
    have h1 := SecpCt.extract_append_left (xonlyBytes p) ByteArray.empty
    rw [ByteArray.append_empty, hxsz] at h1
    exact h1
  unfold parseXonly
  simp only [show ¬ (xonlyBytes p).size < 32 by omega, ↓reduceIte, hx_ext]
  show found (SecpCt.parseXOnly p.xBytes) = _
  rw [SecpCt.parseXOnly_xBytes hp]
  rfl

/-- **Tweaking an x-only key is tweaking the secret key** (BIP 341's output key, BIP 86, a card's spend
key). For a key `d` with public point `p` and *any* bytes `tw`, `xonlyAdd` on `p`'s x is exactly what
`keypairXonlyAdd d tw` gives, taken to its public point and written x-only: the same x and parity, or the
same refusal. -/
theorem xonlyAdd_eq_keypairXonlyAdd {d : Secret} {p : Point}
    (hd : d.Valid) (hp : pointOfSecret d = .ok p) (tw : ByteArray) :
    xonlyAdd (xonlyBytes p) tw = (do let d' ← keypairXonlyAdd d tw; return xonlyOf (← pointOfSecret d')) := by
  obtain ⟨hpgood, _⟩ := pointOfSecret_spec hp
  obtain ⟨de, hde_val, hde_sc⟩ := evenSecret_exists hd
  have hpe : pointOfSecret de = .ok (evenPoint p) := by
    unfold pointOfSecret
    rw [hde_sc, evenKey_point hd hp]
    rfl
  have hkeypair : keypairXonlyAdd d tw = privateAdd de tw := by
    unfold keypairXonlyAdd privateAdd
    rw [hde_sc]
  have hcomm := publicAdd_eq_privateAdd hde_val hpe tw
  unfold publicAdd at hcomm
  unfold xonlyAdd
  rw [parseXonly_xonlyBytes hpgood, ok_bind, hkeypair]
  cases htw : tweak32 tw with
  | error e =>
    have hpriv : privateAdd de tw = .error e := by
      unfold privateAdd; rw [htw, error_bind]
    rw [hpriv, error_bind, error_bind]
  | ok t =>
    rw [htw, ok_bind] at hcomm
    rw [ok_bind, hcomm]
    cases privateAdd de tw with
    | error e => rw [error_bind, error_bind, error_bind]
    | ok d' => rw [ok_bind, ok_bind]

/-! ## 3. A key signs for its own Taproot output -/

private theorem extract_all {b : ByteArray} {n : Nat} (h : b.size = n) : b.extract 0 n = b := by
  have h1 := SecpCt.extract_append_left b ByteArray.empty
  rw [ByteArray.append_empty, h] at h1
  exact h1

theorem xonlyBytes_size (p : Point) : (xonlyBytes p).size = 32 := SecpCt.Fe.bytes_size p.x

/-- For a signature of 64 bytes and a key of 32, the wallet's check is the curve code's. -/
theorem schnorrVerify_eq {x msg sig : ByteArray} (hs : sig.size = 64) (hx : x.size = 32) :
    schnorrVerify x msg sig = .ok (SecpCt.verify sig msg x) := by
  unfold schnorrVerify
  simp +zetaHave only [hs, hx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl,
    extract_all hx]
  rfl

/-- The public key the signer computes from a key's bytes is the key's point, x-only, with its parity. -/
theorem publicKey_bytes {d : Secret} {p : Point} (hd : d.Valid) (hp : pointOfSecret d = .ok p) :
    SecpCt.publicKey d.bytes = some (xonlyBytes p, if p.y.toNat % 2 = 1 then 1 else 0) := by
  obtain ⟨hpgood, hpspec⟩ := pointOfSecret_spec hp
  have hd_sz : d.bytes.size = 32 := SecpCt.Sc.bytes_size d.scalar
  have hd_fb : Secp.fromBE d.bytes = d.scalar.toNat := SecpCt.Sc.fromBE_bytes d.scalar
  have hpt : Spec.smul (Secp.fromBE d.bytes) Spec.G = .pt p.x.toF p.y.toF := by
    rw [hd_fb]; exact hpspec.symm
  rw [SecpCt.publicKey_spec d.bytes hd_sz (by rw [hd_fb]; exact hd.1) (by rw [hd_fb]; exact hd.2) hpt]
  have hxv : p.x.toF.val = p.x.toNat := by rw [SecpCt.Fe.toF_val]; exact Nat.mod_eq_of_lt hpgood.1
  have hyv : p.y.toF.val = p.y.toNat := by rw [SecpCt.Fe.toF_val]; exact Nat.mod_eq_of_lt hpgood.2.1
  rw [hxv, hyv, ← SecpCt.Fe.bytes_spec]
  rfl

/-- **A signature the wallet makes with a key verifies under that key's x-only public key.** -/
theorem schnorrSign_verifies {d : Secret} {p : Point} (hd : d.Valid) (hp : pointOfSecret d = .ok p)
    {msg aux sig : ByteArray} (h : schnorrSign d msg aux = .ok sig) :
    schnorrVerify (xonlyBytes p) msg sig = .ok true := by
  unfold schnorrSign at h
  split at h
  · rw [throw_eq] at h; cases h
  · have hs := found_ok h
    rw [SecpCt.signVerified_eq_sign] at hs
    obtain ⟨key, hpk, hver⟩ := SecpCt.verify_sign hs
    rw [publicKey_bytes hd hp] at hpk
    injection hpk with hkey
    subst hkey
    have hver' : SecpCt.verify sig msg (xonlyBytes p) = true := hver
    rw [schnorrVerify_eq (SecpCt.verify_sound hver').1 (xonlyBytes_size p), hver']

/-- The reference signs whenever the key has a point and the number it signs with is not zero. -/
private theorem signWith_some {m aux : ByteArray} {d0 px py : Nat} (haux : aux.size = 32)
    (hg : Spec.mulG d0 = some (px, py))
    (hk : Secp.hashMod (Secp.Sha256.tagged "BIP0340/nonce"
      (Secp.xorBytes (Secp.toBE32 (if py % 2 = 1 then Secp.negN d0 else d0))
        (Secp.Sha256.tagged "BIP0340/aux" aux) ++ Secp.toBE32 px ++ m)) ≠ 0) :
    ∃ sig, Secp.Bip340.signWith Spec.mulG m d0 aux = some (sig, Secp.toBE32 px) := by
  unfold Secp.Bip340.signWith
  simp +zetaHave only [haux, ne_eq, not_true_eq_false, ↓reduceIte, hg, hk]
  generalize hk0 : Secp.hashMod (Secp.Sha256.tagged "BIP0340/nonce"
      (Secp.xorBytes (Secp.toBE32 (if py % 2 = 1 then Secp.negN d0 else d0))
        (Secp.Sha256.tagged "BIP0340/aux" aux) ++ Secp.toBE32 px ++ m)) = k0 at hk ⊢
  have hlt : k0 < Spec.N := by
    rw [← hk0]; unfold Secp.hashMod; exact Nat.mod_lt _ (by decide)
  have hne := SecpCt.smul_G_ne_inf (Nat.pos_of_ne_zero hk) hlt
  have hpoint : ∃ rx ry, Spec.mulG k0 = some (rx, ry) := by
    unfold Spec.mulG
    cases hs : Spec.smul k0 Spec.G with
    | inf => exact absurd hs hne
    | pt x y => exact ⟨x.val, y.val, rfl⟩
  obtain ⟨rx, ry, hm⟩ := hpoint
  simp +zetaHave only [hm]
  exact ⟨_, rfl⟩

private theorem toF_val_x {p : Point} (hp : p.Good) : p.x.toF.val = p.x.toNat := by
  rw [SecpCt.Fe.toF_val]; exact Nat.mod_eq_of_lt hp.1

private theorem toF_val_y {p : Point} (hp : p.Good) : p.y.toF.val = p.y.toNat := by
  rw [SecpCt.Fe.toF_val]; exact Nat.mod_eq_of_lt hp.2.1

private theorem smul_of_point {d : Secret} {p : Point} (hp : pointOfSecret d = .ok p) :
    Spec.smul d.scalar.toNat Spec.G = .pt p.x.toF p.y.toF :=
  (pointOfSecret_spec hp).2.symm

private theorem mulG_of_smul {k : Nat} {x y : Spec.F} (hs : Spec.smul k Spec.G = .pt x y) :
    Spec.mulG k = some (x.val, y.val) := by
  unfold Spec.mulG
  rw [hs]

private theorem mulG_of_point {d : Secret} {p : Point} (hp : pointOfSecret d = .ok p) :
    Spec.mulG d.scalar.toNat = some (p.x.toNat, p.y.toNat) := by
  obtain ⟨hpgood, _⟩ := pointOfSecret_spec hp
  rw [mulG_of_smul (smul_of_point hp), toF_val_x hpgood, toF_val_y hpgood]

private theorem evenKey_bytes {d : Secret} {p : Point} (hd : d.Valid) (hp : pointOfSecret d = .ok p) :
    Secp.toBE32 (if p.y.toNat % 2 = 1 then Secp.negN d.scalar.toNat else d.scalar.toNat) =
      (SecpCt.evenKey d.scalar).bytes := by
  obtain ⟨hpgood, _⟩ := pointOfSecret_spec hp
  have hnat := SecpCt.evenKey_spec d.scalar hd.2 (smul_of_point hp)
  rw [toF_val_y hpgood] at hnat
  rw [SecpCt.Sc.bytes_spec, hnat]
  unfold Secp.negN
  rw [SecpCt.N_eq]

private theorem nonce_ne {d : Secret} {p : Point} (hd : d.Valid) (hp : pointOfSecret d = .ok p)
    {msg aux : ByteArray}
    (hnonce : bip340Nonce (SecpCt.evenKey d.scalar).bytes (xonlyBytes p) msg aux ≠ 0) :
    Secp.hashMod (Secp.Sha256.tagged "BIP0340/nonce"
      (Secp.xorBytes (Secp.toBE32 (if p.y.toNat % 2 = 1 then Secp.negN d.scalar.toNat else d.scalar.toNat))
        (Secp.Sha256.tagged "BIP0340/aux" aux) ++ Secp.toBE32 p.x.toNat ++ msg)) ≠ 0 := by
  have hpx : Secp.toBE32 p.x.toNat = xonlyBytes p := (SecpCt.Fe.bytes_spec p.x).symm
  rw [evenKey_bytes hd hp, hpx]
  unfold bip340Nonce at hnonce
  exact hnonce

/-- **The wallet's signing never fails for a key**, given 32 bytes of randomness, unless BIP 340's own
number for the signature comes out zero (one hash value in 2²⁵⁶, where BIP 340 itself says to fail). -/
theorem schnorrSign_complete {d : Secret} {p : Point} (hd : d.Valid) (hp : pointOfSecret d = .ok p)
    {msg aux : ByteArray} (haux : aux.size = 32)
    (hnonce : bip340Nonce (SecpCt.evenKey d.scalar).bytes (xonlyBytes p) msg aux ≠ 0) :
    ∃ sig, schnorrSign d msg aux = .ok sig := by
  have hd_sz : d.bytes.size = 32 := SecpCt.Sc.bytes_size d.scalar
  have hd_fb : Secp.fromBE d.bytes = d.scalar.toNat := SecpCt.Sc.fromBE_bytes d.scalar
  obtain ⟨sig, href⟩ := signWith_some (m := msg) haux (mulG_of_point hp) (nonce_ne hd hp hnonce)
  rw [← hd_fb] at href
  have hsign : SecpCt.sign d.bytes msg aux = some sig :=
    SecpCt.sign_eq d.bytes msg aux hd_sz (by rw [hd_fb]; exact hd.2) href
  refine ⟨sig, ?_⟩
  unfold schnorrSign
  simp only [haux, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [SecpCt.signVerified_eq_sign, hsign, found_some]

/-- **A key can spend what is locked to its x-only public key.** For 32 bytes that are a key `d` with
public point `p`, `KeyPathSpendable secret (OP_1 <x of p>)`: every signature the wallet makes with `d`
verifies under the key in the script, and the wallet's signing succeeds for any message with 32 bytes of
randomness, short of BIP 340's zero nonce. -/
theorem keyPathSpendable_of_secret {secret : ByteArray} {d : Secret} {p : Point}
    (hsec : secretOf secret = .ok d) (hpt : pointOfSecret d = .ok p) :
    KeyPathSpendable secret (p2trScript (xonlyBytes p)) := by
  obtain ⟨hd, _, _, _⟩ := secretOf_valid hsec
  refine ⟨d, p, hsec, hpt, xonlyBytes_size p, rfl, ?_, ?_⟩
  · intro msg aux sig h
    exact schnorrSign_verifies hd hpt h
  · intro msg aux haux hnonce
    obtain ⟨sig, hsig⟩ := schnorrSign_complete hd hpt haux hnonce
    exact ⟨sig, hsig, schnorrSign_verifies hd hpt hsig⟩

/-! ## 4. BIP 32 Watch/Sign Derivation Homomorphism -/

theorem publicKeyOf_ok_iff {sk pub : ByteArray} :
    publicKeyOf sk = .ok pub ↔
      ∃ d p, secretOf sk = .ok d ∧ pointOfSecret d = .ok p ∧ pub = serializeCompressed p := by
  unfold publicKeyOf
  constructor
  · intro h
    cases hs : secretOf sk with
    | error e => rw [hs, error_bind] at h; cases h
    | ok d =>
      rw [hs, ok_bind] at h
      cases hp : pointOfSecret d with
      | error e => rw [hp, error_bind] at h; cases h
      | ok p =>
        rw [hp, ok_bind] at h
        simp only [↓reduceIte] at h
        rw [pure_eq] at h
        injection h with h
        exact ⟨d, p, rfl, hp, h.symm⟩
  · rintro ⟨d, p, hs, hp, rfl⟩
    rw [hs, ok_bind, hp, ok_bind]
    rfl

/-- A point written out compressed reads back as itself. -/
theorem parsePublicKey_serializeCompressed {p : Point} (hp : p.Good) :
    parsePublicKey (serializeCompressed p) = .ok p := by
  unfold parsePublicKey serializeCompressed
  simp only [SecpCt.Affine.compressed_size p, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true,
    SecpCt.parseCompressed_compressed hp]
  rfl

/-- The 32 bytes `child` adds to a key at `index`: the left half of the HMAC over `data` and the index. -/
abbrev childTweak (k : HDKey) (index : UInt32) (data : ByteArray) : ByteArray :=
  (hmacSha512 k.chainCode (data ++ u32BE index)).extract 0 32

/-- The child `child` returns at `index`, given its keys: one level down, under the parent's fingerprint,
with the right half of the HMAC as its chain code. -/
abbrev childWith (k : HDKey) (index : UInt32) (data : ByteArray) (priv : Option ByteArray)
    (pub : ByteArray) : HDKey :=
  { depth := k.depth + 1, parentFingerprint := k.fingerprint, childIndex := index,
    chainCode := (hmacSha512 k.chainCode (data ++ u32BE index)).extract 32 64, privateKey := priv,
    publicKey := pub }

/-- What a private key hashes for its child at `index`: its secret behind a zero byte for a hardened
index, its public key otherwise. -/
abbrev childData (k : HDKey) (sk : ByteArray) (index : UInt32) : ByteArray :=
  if index ≥ HDKey.hardenedOffset then ByteArray.mk #[0] ++ sk else k.publicKey

/-! `child`, case by case. Each is `child` unfolded once, with the steps inside it rewritten by what they
are known to return. -/

theorem HDKey.child_depthExhausted {k : HDKey} (index : UInt32) (hdepth : (k.depth == 255) = true) :
    k.child index = .error .depthExhausted := by
  unfold HDKey.child
  simp only [hdepth, ↓reduceIte]
  rw [throw_eq, error_bind]

/-- With a private key: a tweak that cannot be added is `derivationFailed`. -/
theorem HDKey.child_private_error {k : HDKey} {sk : ByteArray} {d : Secret} {index : UInt32} {e : P256KError}
    (hdepth : (k.depth == 255) = false) (hsk : k.privateKey = some sk) (hsec : secretOf sk = .ok d)
    (hpa : privateAdd d (childTweak k index (childData k sk index)) = .error e) :
    k.child index = .error .derivationFailed := by
  have hM : (secretOf sk >>= fun d => privateAdd d (childTweak k index (childData k sk index)) >>= fun s =>
      pointOfSecret s >>= fun q =>
        (pure (childWith k index (childData k sk index) (some s.bytes) (serializeCompressed q)) : PK HDKey)) =
      .error e := by
    rw [hsec, ok_bind, hpa, error_bind]
  unfold HDKey.child
  simp only [hdepth, Bool.false_eq_true, ↓reduceIte, hsk]
  by_cases hh : index ≥ HDKey.hardenedOffset
  · simp only [childData, hh, ↓reduceIte] at hM ⊢
    rw [pure_eq, ok_bind, hM]
    rfl
  · simp only [childData, hh, ↓reduceIte] at hM ⊢
    rw [pure_eq, ok_bind, hM]
    rfl

/-- With a private key: the child's secret is the parent's plus the tweak, and its public key is that
secret's point. -/
theorem HDKey.child_private_ok {k : HDKey} {sk : ByteArray} {d s : Secret} {ps : Point} {index : UInt32}
    (hdepth : (k.depth == 255) = false) (hsk : k.privateKey = some sk) (hsec : secretOf sk = .ok d)
    (hpa : privateAdd d (childTweak k index (childData k sk index)) = .ok s)
    (hps : pointOfSecret s = .ok ps) :
    k.child index =
      .ok (childWith k index (childData k sk index) (some s.bytes) (serializeCompressed ps)) := by
  have hM : (secretOf sk >>= fun d => privateAdd d (childTweak k index (childData k sk index)) >>= fun s =>
      pointOfSecret s >>= fun q =>
        (pure (childWith k index (childData k sk index) (some s.bytes) (serializeCompressed q)) : PK HDKey)) =
      .ok (childWith k index (childData k sk index) (some s.bytes) (serializeCompressed ps)) := by
    rw [hsec, ok_bind, hpa, ok_bind, hps, ok_bind, pure_eq]
  unfold HDKey.child
  simp only [hdepth, Bool.false_eq_true, ↓reduceIte, hsk]
  by_cases hh : index ≥ HDKey.hardenedOffset
  · simp only [childData, hh, ↓reduceIte] at hM ⊢
    rw [pure_eq, ok_bind, hM]
    rfl
  · simp only [childData, hh, ↓reduceIte] at hM ⊢
    rw [pure_eq, ok_bind, hM]
    rfl

/-- With a public key, at an index that is not hardened: a tweak that cannot be added is
`derivationFailed`. -/
theorem HDKey.child_public_error {k : HDKey} {p : Point} {index : UInt32} {e : P256KError}
    (hdepth : (k.depth == 255) = false) (hpriv : k.privateKey = none)
    (hnh : ¬ index ≥ HDKey.hardenedOffset) (hpub : parsePublicKey k.publicKey = .ok p)
    (hpa : publicAdd p (childTweak k index k.publicKey) = .error e) :
    k.child index = .error .derivationFailed := by
  have hM : (parsePublicKey k.publicKey >>= fun p => publicAdd p (childTweak k index k.publicKey) >>= fun q =>
      (pure (childWith k index k.publicKey none (serializeCompressed q)) : PK HDKey)) = .error e := by
    rw [hpub, ok_bind, hpa, error_bind]
  unfold HDKey.child
  simp only [hdepth, Bool.false_eq_true, ↓reduceIte, hpriv, hnh]
  rw [pure_eq, ok_bind, hM]
  rfl

/-- With a public key, at an index that is not hardened: the child's public key is the parent's point plus
the tweak's. -/
theorem HDKey.child_public_ok {k : HDKey} {p q : Point} {index : UInt32}
    (hdepth : (k.depth == 255) = false) (hpriv : k.privateKey = none)
    (hnh : ¬ index ≥ HDKey.hardenedOffset) (hpub : parsePublicKey k.publicKey = .ok p)
    (hpa : publicAdd p (childTweak k index k.publicKey) = .ok q) :
    k.child index = .ok (childWith k index k.publicKey none (serializeCompressed q)) := by
  have hM : (parsePublicKey k.publicKey >>= fun p => publicAdd p (childTweak k index k.publicKey) >>= fun q =>
      (pure (childWith k index k.publicKey none (serializeCompressed q)) : PK HDKey)) =
      .ok (childWith k index k.publicKey none (serializeCompressed q)) := by
    rw [hpub, ok_bind, hpa, ok_bind, pure_eq]
  unfold HDKey.child
  simp only [hdepth, Bool.false_eq_true, ↓reduceIte, hpriv, hnh]
  rw [pure_eq, ok_bind, hM]
  rfl

/-- **A private key's child is a private key.** If a key's public key is its secret's point, so is its
child's, at any index, hardened or not. -/
theorem HDKey.child_preserves_wellFormed {k ck : HDKey} {index : UInt32}
    (hwf : WellFormedPrivateHDKey k) (hchild : k.child index = .ok ck) :
    WellFormedPrivateHDKey ck := by
  obtain ⟨sk, hsk, hpub⟩ := hwf
  obtain ⟨d, p, hsec, _, _⟩ := publicKeyOf_ok_iff.mp hpub
  obtain ⟨hd, _, _, _⟩ := secretOf_valid hsec
  cases hdep : k.depth == 255 with
  | true => rw [HDKey.child_depthExhausted index hdep] at hchild; cases hchild
  | false =>
    cases hpa : privateAdd d (childTweak k index (childData k sk index)) with
    | error e => rw [HDKey.child_private_error hdep hsk hsec hpa] at hchild; cases hchild
    | ok s =>
      obtain ⟨hs_val, _⟩ := privateAdd_valid hd hpa
      obtain ⟨ps, hps, _, _⟩ := pointOfSecret_complete hs_val
      rw [HDKey.child_private_ok hdep hsk hsec hpa hps] at hchild
      injection hchild with hchild
      subst hchild
      exact ⟨s.bytes, rfl, publicKeyOf_ok_iff.mpr ⟨s, ps, secretOf_bytes hs_val, hps, rfl⟩⟩

/-- **A watch-only key derives what the signing key derives** (BIP 32). For a private key whose public key
is its secret's point and an index that is not hardened, deriving the child and then dropping its secret is
exactly deriving the child of the key with its secret dropped: the same child, or the same refusal. So an
address the wallet shows from its public keys is one its private keys can sign for. -/
theorem HDKey.child_neutered_comm {k : HDKey} {index : UInt32}
    (hwf : WellFormedPrivateHDKey k) (hnh : index < HDKey.hardenedOffset) :
    (k.child index).map HDKey.neutered = k.neutered.child index := by
  obtain ⟨sk, hsk, hpub⟩ := hwf
  obtain ⟨d, p, hsec, hp, hkpub⟩ := publicKeyOf_ok_iff.mp hpub
  obtain ⟨hd, _, _, _⟩ := secretOf_valid hsec
  obtain ⟨hpgood, _⟩ := pointOfSecret_spec hp
  have hnot : ¬ index ≥ HDKey.hardenedOffset := by
    simp only [ge_iff_le, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt] at hnh ⊢
    omega
  have hdata : childData k sk index = k.publicKey := by
    simp only [childData, hnot, ↓reduceIte]
  have hpriv : k.neutered.privateKey = none := rfl
  have hnpub : k.neutered.publicKey = k.publicKey := rfl
  have hnchain : k.neutered.chainCode = k.chainCode := rfl
  cases hdep : k.depth == 255 with
  | true =>
    have hdep' : (k.neutered.depth == 255) = true := hdep
    rw [HDKey.child_depthExhausted index hdep, HDKey.child_depthExhausted index hdep']
    rfl
  | false =>
    have hdep' : (k.neutered.depth == 255) = false := hdep
    have hparse : parsePublicKey k.neutered.publicKey = .ok p := by
      rw [hnpub, hkpub]; exact parsePublicKey_serializeCompressed hpgood
    have hcomm := publicAdd_eq_privateAdd hd hp (childTweak k index k.publicKey)
    have htw : childTweak k.neutered index k.neutered.publicKey = childTweak k index k.publicKey := rfl
    cases hpa : privateAdd d (childTweak k index k.publicKey) with
    | error e =>
      rw [hpa, error_bind] at hcomm
      rw [← hdata] at hpa
      rw [← htw] at hcomm
      rw [HDKey.child_private_error hdep hsk hsec hpa,
        HDKey.child_public_error hdep' hpriv hnot hparse hcomm]
      rfl
    | ok s =>
      rw [hpa, ok_bind] at hcomm
      obtain ⟨hs_val, _⟩ := privateAdd_valid hd hpa
      obtain ⟨ps, hps, _, _⟩ := pointOfSecret_complete hs_val
      rw [hps] at hcomm
      rw [← hdata] at hpa
      rw [← htw] at hcomm
      rw [HDKey.child_private_ok hdep hsk hsec hpa hps,
        HDKey.child_public_ok hdep' hpriv hnot hparse hcomm, hdata]
      rfl

/-- The same for two steps, as an account key derives an address's key: chain, then index. -/
theorem HDKey.child2_neutered_comm {k : HDKey} {chain index : UInt32}
    (hwf : WellFormedPrivateHDKey k)
    (hc : chain < HDKey.hardenedOffset) (hi : index < HDKey.hardenedOffset) :
    (k.child chain >>= fun c => c.child index).map HDKey.neutered =
      (k.neutered.child chain >>= fun c => c.child index) := by
  rw [← HDKey.child_neutered_comm hwf hc]
  cases hc_res : k.child chain with
  | error e => rfl
  | ok ck =>
    have hwf_ck := HDKey.child_preserves_wellFormed hwf hc_res
    show (ck.child index).map HDKey.neutered = ck.neutered.child index
    exact HDKey.child_neutered_comm hwf_ck hi

/-! ## 5. Taproot and BIP 86: the key behind an output, and the leaves committed in it -/

/-- An output key that `tweakedOutputKey` returns is the 32-byte internal key with its tweak added. -/
theorem Taproot.tweakedOutputKey_ok {ik : ByteArray} {root : Option ByteArray} {r : ByteArray × Bool}
    (h : Taproot.tweakedOutputKey ik root = .ok r) :
    ik.size = 32 ∧ xonlyAdd ik (Taproot.tweak ik root) = .ok r := by
  unfold Taproot.tweakedOutputKey at h
  by_cases hsz : (ik.size != 32) = true
  · simp only [hsz, ↓reduceIte] at h
    rw [throw_eq, error_bind] at h
    cases h
  · simp only [hsz, Bool.false_eq_true, ↓reduceIte] at h
    have hsz32 : ik.size = 32 := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsz
      exact hsz
    cases hx : xonlyAdd ik (Taproot.tweak ik root) with
    | error e => rw [hx] at h; cases h
    | ok r' =>
      rw [hx] at h
      injection h with h
      rw [h]
      exact ⟨hsz32, rfl⟩

theorem Taproot.tweakedOutputKey_of_ok {ik : ByteArray} {root : Option ByteArray} {r : ByteArray × Bool}
    (hsz : ik.size = 32) (hx : xonlyAdd ik (Taproot.tweak ik root) = .ok r) :
    Taproot.tweakedOutputKey ik root = .ok r := by
  unfold Taproot.tweakedOutputKey
  simp only [hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hx]
  rfl

/-- A script that `scriptPubKey` returns is `OP_1` and the tweaked output key. -/
theorem Taproot.scriptPubKey_ok {ik : ByteArray} {root : Option ByteArray} {spk : ByteArray}
    (h : Taproot.scriptPubKey ik root = .ok spk) :
    ∃ r, Taproot.tweakedOutputKey ik root = .ok r ∧ spk = p2trScript r.1 := by
  unfold Taproot.scriptPubKey at h
  cases ht : Taproot.tweakedOutputKey ik root with
  | error e => rw [ht, error_bind] at h; cases h
  | ok r =>
    rw [ht, ok_bind, pure_eq] at h
    injection h with h
    exact ⟨r, rfl, h.symm⟩

/-- **The key behind a Taproot output can spend it by its key path**, with a script tree or without. For
a key `d` with public point `p`: whenever the wallet makes the output script from `p`'s x-only key (and a
Merkle root, if there is a tree), `keypairXonlyAdd` gives the tweaked secret `d'`, the script is `OP_1` and
the x of `d'`'s point, and `d'` can sign for it (`KeyPathSpendable`). -/
theorem Taproot.keyPath_spendable {d : Secret} {p : Point} {merkleRoot : Option ByteArray} {spk : ByteArray}
    (hd : d.Valid) (hpt : pointOfSecret d = .ok p)
    (hspk : Taproot.scriptPubKey (xonlyBytes p) merkleRoot = .ok spk) :
    ∃ d' p', keypairXonlyAdd d (Taproot.tweak (xonlyBytes p) merkleRoot) = .ok d' ∧ d'.Valid ∧
      pointOfSecret d' = .ok p' ∧
      xonlyAdd (xonlyBytes p) (Taproot.tweak (xonlyBytes p) merkleRoot) = .ok (xonlyOf p') ∧
      spk = p2trScript (xonlyBytes p') ∧
      KeyPathSpendable d'.bytes spk := by
  obtain ⟨r, hr, hspk_eq⟩ := Taproot.scriptPubKey_ok hspk
  obtain ⟨_, hx⟩ := Taproot.tweakedOutputKey_ok hr
  have hx' := hx
  rw [xonlyAdd_eq_keypairXonlyAdd hd hpt] at hx'
  cases hk : keypairXonlyAdd d (Taproot.tweak (xonlyBytes p) merkleRoot) with
  | error e => rw [hk, error_bind] at hx'; cases hx'
  | ok d' =>
    rw [hk, ok_bind] at hx'
    have hv := keypairXonlyAdd_valid hd hk
    obtain ⟨p', hp', _, _⟩ := pointOfSecret_complete hv
    rw [hp', ok_bind, pure_eq] at hx'
    injection hx' with hx'
    subst hx'
    subst hspk_eq
    exact ⟨d', p', rfl, hv, hp', hx, rfl, keyPathSpendable_of_secret (secretOf_bytes hv) hp'⟩

/-- A compressed public key without its first byte is the point's x. -/
theorem xonly_of_compressed (p : Point) :
    (serializeCompressed p).extract 1 (serializeCompressed p).size = xonlyBytes p := by
  have h1 : (ByteArray.mk #[(2 ||| p.y.isOdd).toUInt8]).size = 1 := rfl
  have h32 : p.x.bytes.size = 32 := SecpCt.Fe.bytes_size p.x
  have hsl := SecpCt.extract_append_right (ByteArray.mk #[(2 ||| p.y.isOdd).toUInt8]) p.x.bytes
  rw [h1] at hsl
  show (p.compressed).extract 1 (p.compressed).size = p.x.bytes
  rw [SecpCt.Affine.compressed_size]
  rw [h32] at hsl
  exact hsl

private theorem p2tr_extract {x : ByteArray} (h : x.size = 32) : (p2trScript x).extract 2 34 = x := by
  have hsl := SecpCt.extract_append_right (ByteArray.mk #[0x51, 0x20]) x
  rw [show (ByteArray.mk #[0x51, 0x20]).size = 2 from rfl, h] at hsl
  exact hsl

/-- **An address the wallet shows is one it can sign for** (BIP 86, the wallet's own receive and change
addresses). For an account key whose public key is its secret's point, and a chain and an index that are not
hardened: whenever the watch-only derivation gives a key and the script for it, the private derivation gives
the matching private key, `tweakedPrivateKey` gives the secret that signs, the script is `OP_1` and that
secret's x-only key, and the secret can sign for the script (`KeyPathSpendable`). -/
theorem BIP86.tweakedPrivateKey_spendable {account pubKey : HDKey} {chain index : UInt32} {spk : ByteArray}
    (hwf : WellFormedPrivateHDKey account)
    (hc : chain < HDKey.hardenedOffset) (hi : index < HDKey.hardenedOffset)
    (hwatch : (account.neutered.child chain >>= fun c => c.child index) = .ok pubKey)
    (hspk : Taproot.scriptPubKey (BIP86.xonlyPublicKey pubKey) none = .ok spk) :
    ∃ privKey sk tweakedSk,
      (account.child chain >>= fun c => c.child index) = .ok privKey ∧
      privKey.neutered = pubKey ∧
      privKey.privateKey = some sk ∧
      BIP86.tweakedPrivateKey sk = .ok tweakedSk ∧
      BIP86.tweakedOutputKey (BIP86.xonlyPublicKey pubKey) = .ok (spk.extract 2 34) ∧
      KeyPathSpendable tweakedSk spk := by
  have hcomm := HDKey.child2_neutered_comm hwf hc hi
  rw [hwatch] at hcomm
  cases hpriv : (account.child chain >>= fun c => c.child index) with
  | error e => rw [hpriv] at hcomm; cases hcomm
  | ok privKey =>
    rw [hpriv] at hcomm
    injection hcomm with hcomm
    have hwf_priv : WellFormedPrivateHDKey privKey := by
      cases hc1 : account.child chain with
      | error e => rw [hc1, error_bind] at hpriv; cases hpriv
      | ok mid =>
        rw [hc1, ok_bind] at hpriv
        exact HDKey.child_preserves_wellFormed (HDKey.child_preserves_wellFormed hwf hc1) hpriv
    obtain ⟨sk, hsk, hpub_sk⟩ := hwf_priv
    obtain ⟨d, p, hsec, hpt, hcomp⟩ := publicKeyOf_ok_iff.mp hpub_sk
    obtain ⟨hd, _, _, _⟩ := secretOf_valid hsec
    have hxonly : BIP86.xonlyPublicKey pubKey = xonlyBytes p := by
      rw [← hcomm]
      show privKey.publicKey.extract 1 privKey.publicKey.size = _
      rw [hcomp]
      exact xonly_of_compressed p
    rw [hxonly] at hspk ⊢
    obtain ⟨d', p', hk, hv, hp', hx, hspk_eq, hspend⟩ := Taproot.keyPath_spendable hd hpt hspk
    have htweak : Taproot.tweak (xonlyBytes p) none = taggedHash "TapTweak" (xonlyBytes p) := by
      unfold Taproot.tweak
      rw [Option.getD_none, ByteArray.append_empty]
    rw [htweak] at hk hx
    have htw_priv : BIP86.tweakedPrivateKey sk = .ok d'.bytes := by
      unfold BIP86.tweakedPrivateKey
      rw [hsec, ok_bind, hpt, ok_bind]
      show (keypairXonlyAdd d (taggedHash "TapTweak" (xonlyBytes p)) >>= fun r => pure r.bytes) = _
      rw [hk, ok_bind, pure_eq]
    have htw_out : BIP86.tweakedOutputKey (xonlyBytes p) = .ok (spk.extract 2 34) := by
      unfold BIP86.tweakedOutputKey
      show (xonlyAdd (xonlyBytes p) (taggedHash "TapTweak" (xonlyBytes p)) >>= fun r => pure r.1) = _
      rw [hx, ok_bind, pure_eq, hspk_eq, p2tr_extract (xonlyBytes_size p')]
      rfl
    exact ⟨privKey, sk, d'.bytes, rfl, hcomm, hsk, htw_priv, htw_out, hspend⟩

/-- Every leaf's path, folded from the leaf's hash upward, comes to the tree's root: what a verifier of a
script-path spend computes (BIP 341) is what the wallet committed to. -/
theorem Taproot.hashes_reconstruct (tree : Taproot.Tree) :
    ∀ {v : UInt8} {script : ByteArray} {path : List ByteArray},
      (v, script, path) ∈ (Taproot.hashes tree).2 →
      reconstructMerkleRoot v script path = Taproot.merkleRoot tree := by
  induction tree with
  | leaf lv ls =>
    intro v script path hmem
    simp only [Taproot.hashes, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    rfl
  | branch l r ihl ihr =>
    intro v script path hmem
    unfold Taproot.merkleRoot
    simp only [Taproot.hashes, List.mem_append, List.mem_map] at hmem ⊢
    rcases hmem with ⟨⟨v', s', p'⟩, hml, heq⟩ | ⟨⟨v', s', p'⟩, hmr, heq⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      unfold reconstructMerkleRoot
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hl : List.foldl Taproot.branchHash (Taproot.leafHash v' s') p' = (Taproot.hashes l).1 := ihl hml
      rw [hl]
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      unfold reconstructMerkleRoot
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hr : List.foldl Taproot.branchHash (Taproot.leafHash v' s') p' = (Taproot.hashes r).1 := ihr hmr
      rw [hr, Taproot.branchHash_comm]

/-- A tweaked output key is 32 bytes. -/
theorem Taproot.tweakedOutputKey_size {ik : ByteArray} {root : Option ByteArray} {out : ByteArray} {par : Bool}
    (h : Taproot.tweakedOutputKey ik root = .ok (out, par)) : out.size = 32 := by
  obtain ⟨_, hx⟩ := Taproot.tweakedOutputKey_ok h
  unfold xonlyAdd at hx
  cases hp : parseXonly ik with
  | error e => rw [hp, error_bind] at hx; cases hx
  | ok p =>
    rw [hp, ok_bind] at hx
    cases ht : tweak32 (Taproot.tweak ik root) with
    | error e => rw [ht, error_bind] at hx; cases hx
    | ok t =>
      rw [ht, ok_bind] at hx
      cases hq : found (SecpCt.pointAdd p t) with
      | error e => rw [hq, error_bind] at hx; cases hx
      | ok q =>
        rw [hq, ok_bind, pure_eq] at hx
        injection hx with hx
        have hout : out = xonlyBytes q := (congrArg Prod.fst hx).symm
        rw [hout]
        exact xonlyBytes_size q

/-- **Every control block the wallet makes proves its leaf.** Whenever `controlBlocks` succeeds for an
internal key and a tree, the output script for that key and the tree's root exists, there is one control
block per leaf in order, and each commits its leaf's version and script into that script as BIP 341's
verifier checks it (`ValidScriptPathCommitment`): its path folds to the root, and the internal key tweaked
by the root is the output key with the parity the block states. -/
theorem Taproot.controlBlocks_valid {internalKey : ByteArray} {tree : Taproot.Tree}
    {cbs : List Taproot.ControlBlock}
    (hcb : Taproot.controlBlocks internalKey tree = .ok cbs) :
    ∃ spk,
      Taproot.scriptPubKey internalKey (some (Taproot.merkleRoot tree)) = .ok spk ∧
      cbs.length = (Taproot.hashes tree).2.length ∧
      ∀ (j : Nat) (hj1 : j < cbs.length) (hj2 : j < (Taproot.hashes tree).2.length),
        ValidScriptPathCommitment (cbs[j]'hj1) ((Taproot.hashes tree).2[j]'hj2).1
          ((Taproot.hashes tree).2[j]'hj2).2.1 spk := by
  unfold Taproot.controlBlocks at hcb
  simp +zetaHave only [] at hcb
  cases htw : Taproot.tweakedOutputKey internalKey (some (Taproot.merkleRoot tree)) with
  | error e => rw [htw, error_bind] at hcb; cases hcb
  | ok qp =>
    obtain ⟨outKey, parity⟩ := qp
    rw [htw, ok_bind, pure_eq] at hcb
    injection hcb with hcb
    subst hcb
    have hout_sz : outKey.size = 32 := Taproot.tweakedOutputKey_size htw
    refine ⟨p2trScript outKey, ?_, List.length_map _, ?_⟩
    · unfold Taproot.scriptPubKey
      rw [htw, ok_bind, pure_eq]
      rfl
    · intro j hj1 hj2
      rw [List.getElem_map]
      have hmem := List.getElem_mem hj2
      generalize (Taproot.hashes tree).2[j]'hj2 = leaf at hmem ⊢
      obtain ⟨v, script, path⟩ := leaf
      have hroot := Taproot.hashes_reconstruct tree hmem
      refine ⟨rfl, outKey, hout_sz, rfl, ?_⟩
      show Taproot.tweakedOutputKey internalKey (some (reconstructMerkleRoot v script path)) = _
      rw [hroot]
      exact htw

/-! ## 6. A card for one person: the key that signs for each payment to it -/

/-- A key's bytes read back as a tweak are the key's number. -/
theorem tweak32_bytes {t : Secret} (ht : t.Valid) : tweak32 t.bytes = .ok t.scalar := by
  unfold tweak32
  simp only [show t.bytes.size = 32 from SecpCt.Sc.bytes_size t.scalar, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  show found (SecpCt.scalar? t.scalar.bytes) = _
  rw [SecpCt.scalar?_bytes ht.2]
  rfl

/-- **Adding a key's point is adding the key as a tweak.** For a point `B` and a key `t` with point `T`,
`combine [B, T]` (how BIP 352's sender forms `B + t·G`) is `publicAdd B t`: the same point, or the same
refusal when the sum is the point at infinity. -/
theorem combine_two_eq_publicAdd {B T : Point} {t : Secret}
    (hB : B.Good) (ht : t.Valid) (hT : pointOfSecret t = .ok T) :
    combine [B, T] = publicAdd B t.bytes := by
  obtain ⟨hTgood, hTspec⟩ := pointOfSecret_spec hT
  unfold publicAdd combine
  rw [tweak32_bytes ht, ok_bind]
  have hall : ∀ p ∈ [B, T], p.Good := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hB
    · exact hTgood
  have hsum : ([B, T].foldl (fun sum p => Spec.add sum p.spec) .inf) =
      Spec.add (Spec.smul t.scalar.toNat Spec.G) B.spec := by
    rw [List.foldl_cons, List.foldl_cons, List.foldl_nil, Spec.inf_add, hTspec, Spec.add_comm]
  obtain ⟨hcurve, hrep_c⟩ :=
    SecpCt.sum_rep [B, T] hall SecpCt.Point.infinity .inf trivial SecpCt.rep_infinity
  rw [hsum] at hcurve hrep_c
  have hrep_pa : SecpCt.Rep
      (SecpCt.Point.add (SecpCt.Point.mulPublic t.scalar SecpCt.Point.generator) B.point)
      (Spec.add (Spec.smul t.scalar.toNat Spec.G) B.spec) :=
    SecpCt.rep_add (Spec.smul_onCurve t.scalar.toNat Spec.G_onCurve) hB.2.2
      (SecpCt.mulPublic_rep t.scalar Spec.G_onCurve SecpCt.rep_generator) (SecpCt.Affine.rep hB)
  have hc_def : SecpCt.combine [B, T] =
      ([B, T].foldl (fun sum p => SecpCt.Point.add sum p.point) SecpCt.Point.infinity).toAffine? := by
    unfold SecpCt.combine; rfl
  have hpa_def : SecpCt.pointAdd B t.scalar =
      (SecpCt.Point.add (SecpCt.Point.mulPublic t.scalar SecpCt.Point.generator) B.point).toAffine? := by
    unfold SecpCt.pointAdd; rfl
  cases hc : SecpCt.combine [B, T] with
  | none =>
    cases hpa : SecpCt.pointAdd B t.scalar with
    | none => rfl
    | some q =>
      rw [hc_def] at hc
      have hinf := SecpCt.toAffine?_none hrep_c hc
      obtain ⟨hq, _⟩ := SecpCt.pointAdd_spec hB hpa
      rw [hinf] at hq
      cases hq
  | some q =>
    obtain ⟨hq_spec, hq_good⟩ := SecpCt.combine_spec hall hc
    rw [hsum] at hq_spec
    cases hpa : SecpCt.pointAdd B t.scalar with
    | none =>
      rw [hpa_def] at hpa
      have hinf := SecpCt.toAffine?_none hrep_pa hpa
      rw [hinf] at hq_spec
      cases hq_spec
    | some q' =>
      obtain ⟨hq', hq'_good⟩ := SecpCt.pointAdd_spec hB hpa
      rw [SecpCt.Affine.ext_spec hq_good hq'_good (hq_spec.symm.trans hq')]

/-- BIP 352's tweak for output `k` under a shared secret: `hash_BIP0352/SharedSecret(secret ‖ ser32(k))`. -/
abbrev outputTweakOf (secret : ByteArray) (k : UInt32) : ByteArray :=
  taggedHash "BIP0352/SharedSecret"
    (secret ++ ByteArray.mk #[(k >>> 24).toUInt8, (k >>> 16).toUInt8, (k >>> 8).toUInt8, k.toUInt8])

/-- The sender's output script, when every step succeeds: `OP_1` and the x of `B + t·G`. -/
theorem outputScript_of_ok {secret spendKey : ByteArray} {k : UInt32} {B out : Point}
    (hB : parsePublicKey spendKey = .ok B)
    (hvalid : SilentPaymentSending.isValidScalar (outputTweakOf secret k) = true)
    (hout : (secretOf (outputTweakOf secret k) >>= pointOfSecret >>= fun t => combine [B, t]) = .ok out) :
    SilentPaymentSending.outputScript secret spendKey k = .ok (p2trScript (xonlyBytes out)) := by
  unfold SilentPaymentSending.outputScript
  rw [hB]
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [pure_eq, ok_bind, hout]
  rfl

/-- The sender's output script, when the two points do not add up to a point: refused. -/
theorem outputScript_of_error {secret spendKey : ByteArray} {k : UInt32} {B : Point} {e : P256KError}
    (hB : parsePublicKey spendKey = .ok B)
    (hvalid : SilentPaymentSending.isValidScalar (outputTweakOf secret k) = true)
    (hout : (secretOf (outputTweakOf secret k) >>= pointOfSecret >>= fun t => combine [B, t]) = .error e) :
    SilentPaymentSending.outputScript secret spendKey k = .error .invalidRecipientKey := by
  unfold SilentPaymentSending.outputScript
  rw [hB]
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [pure_eq, ok_bind, hout]
  rfl

/-- The sender's output script, when the tweak is not a scalar: refused. -/
theorem outputScript_of_invalidTweak {secret spendKey : ByteArray} {k : UInt32} {B : Point}
    (hB : parsePublicKey spendKey = .ok B)
    (hvalid : SilentPaymentSending.isValidScalar (outputTweakOf secret k) = false) :
    SilentPaymentSending.outputScript secret spendKey k = .error .invalidTweak := by
  unfold SilentPaymentSending.outputScript
  rw [hB]
  simp only [hvalid, Bool.not_false, ↓reduceIte]
  rw [pure_eq, ok_bind, throw_eq, error_bind]

/-- The sender's output script, when the spend key is not a key: refused. -/
theorem outputScript_of_badKey {secret spendKey : ByteArray} {k : UInt32} {e : P256KError}
    (hB : parsePublicKey spendKey = .error e) :
    SilentPaymentSending.outputScript secret spendKey k = .error .invalidRecipientKey := by
  unfold SilentPaymentSending.outputScript
  rw [hB]
  simp only []
  rw [throw_eq, error_bind]

/-- **What the payer's script for a card is.** If the sender's `outputScript` gives a script for a shared
secret, a spend key that is the point of a key `d`, and an output number, then the tweak is a key, `d` plus
the tweak is a key `s` with a point `P`, and the script is `OP_1` and the x of `P`. -/
theorem outputScript_ok {secret spendKey : ByteArray} {k : UInt32} {d : Secret} {B : Point} {spk : ByteArray}
    (hd : d.Valid) (hpt : pointOfSecret d = .ok B) (hkey : spendKey = serializeCompressed B)
    (h : SilentPaymentSending.outputScript secret spendKey k = .ok spk) :
    isValidSecret (outputTweakOf secret k) = true ∧
    ∃ s P, privateAdd d (outputTweakOf secret k) = .ok s ∧ s.Valid ∧ pointOfSecret s = .ok P ∧
      spk = p2trScript (xonlyBytes P) := by
  obtain ⟨hBgood, _⟩ := pointOfSecret_spec hpt
  have hB : parsePublicKey spendKey = .ok B := by
    rw [hkey]; exact parsePublicKey_serializeCompressed hBgood
  cases hvalid : SilentPaymentSending.isValidScalar (outputTweakOf secret k) with
  | false => rw [outputScript_of_invalidTweak hB hvalid] at h; cases h
  | true =>
    have hvis : isValidSecret (outputTweakOf secret k) = true := hvalid
    obtain ⟨t, ht, ht_val, ht_bytes⟩ := secretOf_of_isValidSecret hvis
    obtain ⟨T, hT, _, _⟩ := pointOfSecret_complete ht_val
    have hsum : (secretOf (outputTweakOf secret k) >>= pointOfSecret >>= fun t => combine [B, t]) =
        (privateAdd d (outputTweakOf secret k) >>= pointOfSecret) := by
      rw [ht, ok_bind, hT, ok_bind, combine_two_eq_publicAdd hBgood ht_val hT, ht_bytes,
        publicAdd_eq_privateAdd hd hpt]
    cases hpa : privateAdd d (outputTweakOf secret k) with
    | error e =>
      rw [hpa, error_bind] at hsum
      rw [outputScript_of_error hB hvalid hsum] at h
      cases h
    | ok s =>
      obtain ⟨hs_val, _⟩ := privateAdd_valid hd hpa
      obtain ⟨P, hP, _, _⟩ := pointOfSecret_complete hs_val
      rw [hpa, ok_bind, hP] at hsum
      rw [outputScript_of_ok hB hvalid hsum] at h
      injection h with h
      exact ⟨hvis, s, P, rfl, hs_val, hP, h.symm⟩

/-- A script `codeScript` returns is the sender's `outputScript` for the code's shared secret and spend
key, and the shared secret is a public key. -/
theorem SilentPaymentPairing.codeScript_ok {c : CardCode} {i : UInt32} {spk : ByteArray}
    (h : SilentPaymentPairing.codeScript c i = .ok spk) :
    SilentPaymentAddress.isValidPublicKey c.sharedSecret = true ∧
    SilentPaymentSending.outputScript c.sharedSecret c.spendKey i = .ok spk := by
  unfold SilentPaymentPairing.codeScript at h
  cases hv : SilentPaymentAddress.isValidPublicKey c.sharedSecret with
  | false =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    rw [throw_eq, error_bind] at h
    cases h
  | true =>
    simp only [hv, ↓reduceIte] at h
    cases ho : SilentPaymentSending.outputScript c.sharedSecret c.spendKey i with
    | error e => rw [ho] at h; cases e <;> cases h
    | ok s =>
      rw [ho] at h
      injection h with h
      rw [h]
      exact ⟨rfl, rfl⟩

private theorem bytes_beq_self (a : ByteArray) : (a == a) = true := by
  show (a.data == a.data) = true
  exact beq_self_eq_true _

/-- The tweak of output `i` under a code, when the code's shared secret is a key and the tweak a scalar. -/
theorem SilentPaymentPairing.codeOutputTweak_of {c : CardCode} {i : UInt32}
    (hv : SilentPaymentAddress.isValidPublicKey c.sharedSecret = true)
    (ht : isValidSecret (outputTweakOf c.sharedSecret i) = true) :
    SilentPaymentPairing.codeOutputTweak c i = .ok (outputTweakOf c.sharedSecret i) := by
  have ht' : isValidSecret
      (taggedHash "BIP0352/SharedSecret" (c.sharedSecret ++ SilentPaymentPairing.ser32 i)) = true := ht
  unfold SilentPaymentPairing.codeOutputTweak
  simp only [hv, ht', ↓reduceIte]
  rfl

theorem SilentPaymentPairing.codeSpendSecret_def :
    SilentPaymentPairing.codeSpendSecret = body% SilentPaymentPairing.codeSpendSecret [] [] := rfl

private theorem codeSpendSecret_model_none {sof : ByteArray → PK Secret}
    {padd : Secret → ByteArray → PK Secret} {pos : Secret → PK Point} {ser : Point → ByteArray}
    {cot : CardCode → UInt32 → SilentPaymentPairing.PP ByteArray} {sb : Secret → ByteArray}
    {spend : ByteArray} {c : CardCode} {i : UInt32} {b s : Secret} {B : Point} {t : ByteArray}
    (hb : sof spend = .ok b) (hB : pos b = .ok B) (heq : (ser B == c.spendKey) = true)
    (hcot : cot c i = .ok t) (hs : padd b t = .ok s) :
    (body% SilentPaymentPairing.codeSpendSecret
      [secretOf, privateAdd, pointOfSecret, serializeCompressed, SilentPaymentPairing.codeOutputTweak,
        Secret.bytes]
      [sof, padd, pos, ser, cot, sb]) spend none c i = .ok (sb s) := by
  simp only [hb, pure, Except.pure, bind, Except.bind, hB, heq, ↓reduceIte, hcot, hs]

private theorem codeSpendSecret_model_some {sof : ByteArray → PK Secret}
    {padd : Secret → ByteArray → PK Secret} {pos : Secret → PK Point} {ser : Point → ByteArray}
    {cot : CardCode → UInt32 → SilentPaymentPairing.PP ByteArray} {sb : Secret → ByteArray}
    {spend l : ByteArray} {c : CardCode} {i : UInt32} {b d s : Secret} {B : Point} {t : ByteArray}
    (hb : sof spend = .ok b) (hl : padd b l = .ok d) (hB : pos d = .ok B)
    (heq : (ser B == c.spendKey) = true) (hcot : cot c i = .ok t) (hs : padd d t = .ok s) :
    (body% SilentPaymentPairing.codeSpendSecret
      [secretOf, privateAdd, pointOfSecret, serializeCompressed, SilentPaymentPairing.codeOutputTweak,
        Secret.bytes]
      [sof, padd, pos, ser, cot, sb]) spend (some l) c i = .ok (sb s) := by
  simp only [hb, pure, Except.pure, bind, Except.bind, hl, hB, heq, ↓reduceIte, hcot, hs]

/-- **The key that signs for a payment to a card is the key the payer's script is locked to.** For the
wallet's spend key `b`, the key `d` a card's spend key is the point of (`b`, or `b` with the person's label:
`CardKey`), and any output number: whenever the payer's `codeScript` gives a script, the wallet's
`codeSpendSecret` succeeds, and the secret it returns can sign for that script (`KeyPathSpendable`). -/
theorem SilentPaymentPairing.codeSpendSecret_spendable
    {spend : ByteArray} {label : Option ByteArray} {b d : Secret} {B : Point}
    {code : CardCode} {i : UInt32} {spk : ByteArray}
    (hb : secretOf spend = .ok b) (hd : CardKey b label d) (hB : pointOfSecret d = .ok B)
    (hkey : serializeCompressed B = code.spendKey)
    (hscript : SilentPaymentPairing.codeScript code i = .ok spk) :
    ∃ sk, SilentPaymentPairing.codeSpendSecret spend label code i = .ok sk ∧ KeyPathSpendable sk spk := by
  obtain ⟨hb_val, _, _, _⟩ := secretOf_valid hb
  have hd_val : d.Valid := by
    cases label with
    | none =>
      have hdb : d = b := hd
      rw [hdb]; exact hb_val
    | some l => exact (privateAdd_valid hb_val hd).1
  obtain ⟨hv, hout⟩ := SilentPaymentPairing.codeScript_ok hscript
  obtain ⟨ht, s, P, hs, hs_val, hP, hspk⟩ := outputScript_ok hd_val hB hkey.symm hout
  have hcot := SilentPaymentPairing.codeOutputTweak_of (i := i) hv ht
  have heq : (serializeCompressed B == code.spendKey) = true := by
    rw [hkey]; exact bytes_beq_self _
  refine ⟨s.bytes, ?_, ?_⟩
  · rw [SilentPaymentPairing.codeSpendSecret_def]
    cases label with
    | none =>
      have hdb : d = b := hd
      rw [hdb] at hB hs
      exact codeSpendSecret_model_none hb hB heq hcot hs
    | some l => exact codeSpendSecret_model_some hb hd hB heq hcot hs
  · rw [hspk]
    exact keyPathSpendable_of_secret (secretOf_bytes hs_val) hP

/-! ### How a card is issued, step by step

Each function that issues a card is read back here: what its parts returned when it returned something. -/

section issuing
open SilentPaymentPairing

private theorem address_model {pko : ByteArray → Bool → PK ByteArray}
    {mk : ByteArray → ByteArray → String → Except SilentPaymentAddressError SilentPaymentAddress}
    {scan spend : ByteArray} {hrp : String} {own : SilentPaymentAddress}
    (h : (body% SilentPaymentPairing.address [publicKeyOf, SilentPaymentAddress.make] [pko, mk])
      scan spend hrp = .ok own) :
    ∃ ps pp, pko scan true = .ok ps ∧ pko spend true = .ok pp ∧ mk ps pp hrp = .ok own := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : pko scan true with
  | error e => simp only [h1, throw, throwThe, MonadExceptOf.throw] at h; cases h
  | ok ps =>
    cases h2 : pko spend true with
    | error e => simp only [h1, h2, throw, throwThe, MonadExceptOf.throw] at h; cases h
    | ok pp =>
      cases h3 : mk ps pp hrp with
      | error e => simp only [h1, h2, h3, throw, throwThe, MonadExceptOf.throw] at h; cases h
      | ok a =>
        simp only [h1, h2, h3] at h
        injection h with h
        exact ⟨ps, pp, rfl, rfl, by rw [h3, h]⟩

theorem SilentPaymentPairing.address_def : SilentPaymentPairing.address = body% SilentPaymentPairing.address [] [] := rfl

/-- An address `address` returns is made of the two keys' public keys. -/
theorem SilentPaymentPairing.address_ok {scan spend : ByteArray} {hrp : String} {own : SilentPaymentAddress}
    (h : SilentPaymentPairing.address scan spend hrp = .ok own) :
    ∃ ps pp, publicKeyOf scan = .ok ps ∧ publicKeyOf spend = .ok pp ∧
      SilentPaymentAddress.make ps pp hrp = .ok own := by
  rw [SilentPaymentPairing.address_def] at h
  exact address_model (pko := @publicKeyOf) (mk := SilentPaymentAddress.make) h

private theorem make_model {v : ByteArray → Bool} {sk pk : ByteArray} {hrp : String} {a : SilentPaymentAddress}
    (h : (body% SilentPaymentAddress.make [SilentPaymentAddress.isValidPublicKey] [v]) sk pk hrp = .ok a) :
    a.spendKey = pk := by
  simp only [] at h
  split at h
  · injection h with h; rw [← h]
  · cases h

theorem SilentPaymentAddress.make_def : SilentPaymentAddress.make = body% SilentPaymentAddress.make [] [] := rfl

/-- An address that is made has the spend key it was made with. -/
theorem SilentPaymentAddress.make_spendKey {sk pk : ByteArray} {hrp : String} {a : SilentPaymentAddress}
    (h : SilentPaymentAddress.make sk pk hrp = .ok a) : a.spendKey = pk := by
  rw [SilentPaymentAddress.make_def] at h
  exact make_model (v := SilentPaymentAddress.isValidPublicKey) h

private theorem labelledSpendKey_model {ppk : ByteArray → Bool → PK Point}
    {padd : Point → ByteArray → PK Point} {ser : Point → ByteArray} {spendKey label key : ByteArray}
    (h : (body% SilentPaymentPairing.labelledSpendKey [parsePublicKey, publicAdd, serializeCompressed]
      [ppk, padd, ser]) spendKey label = .ok key) :
    ∃ p q, ppk spendKey true = .ok p ∧ padd p label = .ok q ∧ key = ser q := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : ppk spendKey true with
  | error e => simp only [h1, throw, throwThe, MonadExceptOf.throw] at h; cases h
  | ok p =>
    cases h2 : padd p label with
    | error e => simp only [h1, h2, throw, throwThe, MonadExceptOf.throw] at h; cases h
    | ok q =>
      simp only [h1, h2] at h
      injection h with h
      exact ⟨p, q, rfl, h2, h.symm⟩

theorem SilentPaymentPairing.labelledSpendKey_def :
    SilentPaymentPairing.labelledSpendKey = body% SilentPaymentPairing.labelledSpendKey [] [] := rfl

/-- A labelled spend key is the spend key's point with the label added, written compressed. -/
theorem SilentPaymentPairing.labelledSpendKey_ok {spendKey label key : ByteArray}
    (h : SilentPaymentPairing.labelledSpendKey spendKey label = .ok key) :
    ∃ p q, parsePublicKey spendKey = .ok p ∧ publicAdd p label = .ok q ∧ key = serializeCompressed q := by
  rw [SilentPaymentPairing.labelledSpendKey_def] at h
  exact labelledSpendKey_model (ppk := @parsePublicKey) (padd := publicAdd) (ser := serializeCompressed) h

private theorem codeForKeys_model {pko : ByteArray → Bool → PK ByteArray}
    {sso : ByteArray → ByteArray → PP ByteArray} {tf lf : ByteArray → UInt32 → PP ByteArray}
    {lsk : ByteArray → ByteArray → PP ByteArray}
    {scan spendKey : ByteArray} {hrp : String} {k : UInt32} {code : CardCode}
    (h : (body% SilentPaymentPairing.codeForKeys
      [publicKeyOf, SilentPaymentPairing.sharedSecretOf, SilentPaymentPairing.tweakFor,
        SilentPaymentPairing.labelFor, SilentPaymentPairing.labelledSpendKey]
      [pko, sso, tf, lf, lsk]) scan spendKey hrp k = .ok code) :
    ∃ label, lf scan k = .ok label ∧ lsk spendKey label = .ok code.spendKey := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : pko scan true with
  | error e => simp only [h1, throw, throwThe, MonadExceptOf.throw] at h; cases h
  | ok scanKey =>
    cases h2 : tf scan k with
    | error e => simp only [h1, h2] at h; cases h
    | ok x =>
      cases h3 : sso scanKey x with
      | error e => simp only [h1, h2, h3] at h; cases h
      | ok secret =>
        cases h4 : lf scan k with
        | error e => simp only [h1, h2, h3, h4] at h; cases h
        | ok label =>
          cases h5 : lsk spendKey label with
          | error e => simp only [h1, h2, h3, h4, h5] at h; cases h
          | ok key =>
            simp only [h1, h2, h3, h4, h5] at h
            injection h with h
            exact ⟨label, rfl, by rw [h5, ← h]⟩

theorem SilentPaymentPairing.codeForKeys_def :
    SilentPaymentPairing.codeForKeys = body% SilentPaymentPairing.codeForKeys [] [] := rfl

/-- A code's spend key is the wallet's spend key under the person's label. -/
theorem SilentPaymentPairing.codeForKeys_ok {scan spendKey : ByteArray} {hrp : String} {k : UInt32}
    {code : CardCode} (h : SilentPaymentPairing.codeForKeys scan spendKey hrp k = .ok code) :
    ∃ label, SilentPaymentPairing.labelFor scan k = .ok label ∧
      SilentPaymentPairing.labelledSpendKey spendKey label = .ok code.spendKey := by
  rw [SilentPaymentPairing.codeForKeys_def] at h
  exact codeForKeys_model (pko := @publicKeyOf) (sso := SilentPaymentPairing.sharedSecretOf)
    (tf := SilentPaymentPairing.tweakFor) (lf := SilentPaymentPairing.labelFor)
    (lsk := SilentPaymentPairing.labelledSpendKey) h

private theorem codeFor_model {addr : ByteArray → ByteArray → String → PP SilentPaymentAddress}
    {cfk : ByteArray → ByteArray → String → UInt32 → PP CardCode}
    {scan spend : ByteArray} {hrp : String} {k : UInt32} {code : CardCode}
    (h : (body% SilentPaymentPairing.codeFor [SilentPaymentPairing.address, SilentPaymentPairing.codeForKeys]
      [addr, cfk]) scan spend hrp k = .ok code) :
    ∃ own, addr scan spend hrp = .ok own ∧ cfk scan own.spendKey hrp k = .ok code := by
  simp only [bind, Except.bind] at h
  cases h1 : addr scan spend hrp with
  | error e => simp only [h1] at h; cases h
  | ok own =>
    simp only [h1] at h
    exact ⟨own, rfl, h⟩

theorem SilentPaymentPairing.codeFor_def :
    SilentPaymentPairing.codeFor = body% SilentPaymentPairing.codeFor [] [] := rfl

theorem SilentPaymentPairing.codeFor_ok {scan spend : ByteArray} {hrp : String} {k : UInt32} {code : CardCode}
    (h : SilentPaymentPairing.codeFor scan spend hrp k = .ok code) :
    ∃ own, SilentPaymentPairing.address scan spend hrp = .ok own ∧
      SilentPaymentPairing.codeForKeys scan own.spendKey hrp k = .ok code := by
  rw [SilentPaymentPairing.codeFor_def] at h
  exact codeFor_model (addr := SilentPaymentPairing.address) (cfk := SilentPaymentPairing.codeForKeys) h

/-- **A code the wallet issues pays to keys the wallet can sign with.** Whenever `codeFor` gives person
`k`'s code from the wallet's scan and spend keys, and the payer's `codeScript` gives a script for it, the
person's label exists, `codeSpendSecret` with that label succeeds, and the secret it returns can sign for the
script (`KeyPathSpendable`). -/
theorem SilentPaymentPairing.codeFor_spendable
    {scan spend : ByteArray} {hrp : String} {k i : UInt32} {code : CardCode} {spk : ByteArray}
    (hcode : SilentPaymentPairing.codeFor scan spend hrp k = .ok code)
    (hscript : SilentPaymentPairing.codeScript code i = .ok spk) :
    ∃ label sk,
      SilentPaymentPairing.labelFor scan k = .ok label ∧
      SilentPaymentPairing.codeSpendSecret spend (some label) code i = .ok sk ∧
      KeyPathSpendable sk spk := by
  obtain ⟨own, hown, hkeys⟩ := SilentPaymentPairing.codeFor_ok hcode
  obtain ⟨ps, pp, _, hpp, hmake⟩ := SilentPaymentPairing.address_ok hown
  have hown_spend := SilentPaymentAddress.make_spendKey hmake
  obtain ⟨label, hlabel, hlsk⟩ := SilentPaymentPairing.codeForKeys_ok hkeys
  obtain ⟨p, q, hparse, hadd, hkey⟩ := SilentPaymentPairing.labelledSpendKey_ok hlsk
  obtain ⟨b, B0, hb, hB0, hpp_eq⟩ := publicKeyOf_ok_iff.mp hpp
  obtain ⟨hb_val, _, _, _⟩ := secretOf_valid hb
  obtain ⟨hB0_good, _⟩ := pointOfSecret_spec hB0
  rw [hown_spend, hpp_eq, parsePublicKey_serializeCompressed hB0_good] at hparse
  injection hparse with hparse
  rw [← hparse, publicAdd_eq_privateAdd hb_val hB0] at hadd
  cases hpa : privateAdd b label with
  | error e => rw [hpa, error_bind] at hadd; cases hadd
  | ok d =>
    rw [hpa, ok_bind] at hadd
    obtain ⟨sk, hsk, hspend⟩ := SilentPaymentPairing.codeSpendSecret_spendable (label := some label)
      hb hpa hadd hkey.symm hscript
    exact ⟨label, sk, hlabel, hsk, hspend⟩

private theorem issue_model {keysOf : HDKey → UInt32 → PP (ByteArray × ByteArray)}
    {addr : ByteArray → ByteArray → String → PP SilentPaymentAddress} {tf : ByteArray → UInt32 → PP ByteArray}
    {master : HDKey} {coinType k : UInt32} {hrp : String} {scan spend : ByteArray} {card : PairingCard}
    (hkeys : keysOf master coinType = .ok (scan, spend))
    (h : (body% SilentPaymentPairing.issue
      [SilentPaymentPairing.keys, SilentPaymentPairing.address, SilentPaymentPairing.tweakFor]
      [keysOf, addr, tf]) master coinType hrp k = .ok card) :
    addr scan spend hrp = .ok card.address := by
  simp only [bind, Except.bind, pure, Except.pure, hkeys] at h
  cases h1 : addr scan spend hrp with
  | error e => simp only [h1] at h; cases h
  | ok a =>
    cases h2 : tf scan k with
    | error e => simp only [h1, h2] at h; cases h
    | ok x =>
      simp only [h1, h2] at h
      injection h with h
      rw [← h]

theorem SilentPaymentPairing.issue_def : SilentPaymentPairing.issue = body% SilentPaymentPairing.issue [] [] := rfl

/-- A 0.9.12 card's address is the address of the wallet's two keys. -/
theorem SilentPaymentPairing.issue_ok {master : HDKey} {coinType k : UInt32} {hrp : String}
    {scan spend : ByteArray} {card : PairingCard}
    (hkeys : SilentPaymentPairing.keys master coinType = .ok (scan, spend))
    (h : SilentPaymentPairing.issue master coinType hrp k = .ok card) :
    SilentPaymentPairing.address scan spend hrp = .ok card.address := by
  rw [SilentPaymentPairing.issue_def] at h
  exact issue_model (keysOf := SilentPaymentPairing.keys) (addr := SilentPaymentPairing.address)
    (tf := SilentPaymentPairing.tweakFor) hkeys h

private theorem codeOf_model {ss : PairingCard → PP ByteArray} {v : ByteArray → Bool}
    {card : PairingCard} {code : CardCode}
    (h : (body% SilentPaymentPairing.codeOf
      [SilentPaymentPairing.sharedSecret, SilentPaymentAddress.isValidPublicKey] [ss, v]) card = .ok code) :
    code.spendKey = card.address.spendKey := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : ss card with
  | error e => simp only [h1] at h; cases h
  | ok secret =>
    simp only [h1] at h
    split at h
    · injection h with h; rw [← h]
    · simp only [throw, throwThe, MonadExceptOf.throw] at h; cases h

theorem SilentPaymentPairing.codeOf_def : SilentPaymentPairing.codeOf = body% SilentPaymentPairing.codeOf [] [] := rfl

/-- The code a 0.9.12 card pays as has the card's own spend key. -/
theorem SilentPaymentPairing.codeOf_spendKey {card : PairingCard} {code : CardCode}
    (h : SilentPaymentPairing.codeOf card = .ok code) : code.spendKey = card.address.spendKey := by
  rw [SilentPaymentPairing.codeOf_def] at h
  exact codeOf_model (ss := SilentPaymentPairing.sharedSecret) (v := SilentPaymentAddress.isValidPublicKey) h

private theorem scriptPubKey_model {co : PairingCard → PP CardCode} {cs : CardCode → UInt32 → PP ByteArray}
    {card : PairingCard} {i : UInt32} {spk : ByteArray}
    (h : (body% SilentPaymentPairing.scriptPubKey [SilentPaymentPairing.codeOf, SilentPaymentPairing.codeScript]
      [co, cs]) card i = .ok spk) :
    ∃ code, co card = .ok code ∧ cs code i = .ok spk := by
  simp only [bind, Except.bind] at h
  cases h1 : co card with
  | error e => simp only [h1] at h; cases h
  | ok code =>
    simp only [h1] at h
    exact ⟨code, rfl, h⟩

theorem SilentPaymentPairing.scriptPubKey_def :
    SilentPaymentPairing.scriptPubKey = body% SilentPaymentPairing.scriptPubKey [] [] := rfl

theorem SilentPaymentPairing.scriptPubKey_ok {card : PairingCard} {i : UInt32} {spk : ByteArray}
    (h : SilentPaymentPairing.scriptPubKey card i = .ok spk) :
    ∃ code, SilentPaymentPairing.codeOf card = .ok code ∧ SilentPaymentPairing.codeScript code i = .ok spk := by
  rw [SilentPaymentPairing.scriptPubKey_def] at h
  exact scriptPubKey_model (co := SilentPaymentPairing.codeOf) (cs := SilentPaymentPairing.codeScript) h

private theorem spendSecret_model {co : PairingCard → PP CardCode}
    {css : ByteArray → Option ByteArray → CardCode → UInt32 → PP ByteArray}
    {spend : ByteArray} {card : PairingCard} {code : CardCode} {i : UInt32}
    (hc : co card = .ok code) :
    (body% SilentPaymentPairing.spendSecret [SilentPaymentPairing.codeOf, SilentPaymentPairing.codeSpendSecret]
      [co, css]) spend card i = css spend none code i := by
  simp only [bind, Except.bind, hc]

theorem SilentPaymentPairing.spendSecret_def :
    SilentPaymentPairing.spendSecret = body% SilentPaymentPairing.spendSecret [] [] := rfl

theorem SilentPaymentPairing.spendSecret_of {spend : ByteArray} {card : PairingCard} {code : CardCode}
    {i : UInt32} (hc : SilentPaymentPairing.codeOf card = .ok code) :
    SilentPaymentPairing.spendSecret spend card i =
      SilentPaymentPairing.codeSpendSecret spend none code i := by
  rw [SilentPaymentPairing.spendSecret_def]
  exact spendSecret_model (co := SilentPaymentPairing.codeOf) (css := SilentPaymentPairing.codeSpendSecret) hc

/-- **A 0.9.12 card pays to keys the wallet can sign with.** Whenever `issue` gives person `k`'s card from
the master key, and the payer's `scriptPubKey` gives a script for it, `spendSecret` with the wallet's spend
key succeeds, and the secret it returns can sign for the script (`KeyPathSpendable`). -/
theorem SilentPaymentPairing.issue_spendable
    {master : HDKey} {coinType k i : UInt32} {hrp : String}
    {scan spend : ByteArray} {card : PairingCard} {spk : ByteArray}
    (hkeys : SilentPaymentPairing.keys master coinType = .ok (scan, spend))
    (hissue : SilentPaymentPairing.issue master coinType hrp k = .ok card)
    (hscript : SilentPaymentPairing.scriptPubKey card i = .ok spk) :
    ∃ sk, SilentPaymentPairing.spendSecret spend card i = .ok sk ∧ KeyPathSpendable sk spk := by
  have haddr := SilentPaymentPairing.issue_ok hkeys hissue
  obtain ⟨ps, pp, _, hpp, hmake⟩ := SilentPaymentPairing.address_ok haddr
  have hspendKey := SilentPaymentAddress.make_spendKey hmake
  obtain ⟨code, hcode, hcs⟩ := SilentPaymentPairing.scriptPubKey_ok hscript
  have hcode_key := SilentPaymentPairing.codeOf_spendKey hcode
  obtain ⟨b, B, hb, hB, hpp_eq⟩ := publicKeyOf_ok_iff.mp hpp
  have hkey : serializeCompressed B = code.spendKey := by rw [hcode_key, hspendKey, hpp_eq]
  obtain ⟨sk, hsk, hspend⟩ := SilentPaymentPairing.codeSpendSecret_spendable (label := none) (d := b)
    hb rfl hB hkey hcs
  exact ⟨sk, by rw [SilentPaymentPairing.spendSecret_of hcode]; exact hsk, hspend⟩

end issuing

end Winnow.Proofs.Custody
