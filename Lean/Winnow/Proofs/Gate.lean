import Secp.Proofs.Gate
import SecpCt.Gate
import Winnow
import Winnow.Proofs.DeviceSyncProofs

/-! # `Winnow/Proofs/Gate.lean`: Single Auditable Verification Gate

Every top-level theorem in `WinnowProofs` (and the foundational curve/DER/signing theorems in `Secp` and
`SecpCt`) is restated here with its **exact full type signature** (`example : <type> := <thm>`), paired
with non-vacuity witnesses where partial/error-returning functions are involved, and checked by
`#assert_all_axioms` to depend only on `[propext, Quot.sound, Classical.choice]`. -/

namespace Winnow.Proofs.Gate

/-! ## Phase 1: Primality, Abelian Group Law, Generator Order `N`, Signing & BIP 66 DER -/

example : Secp.Primes.IsPrime Secp.P := Secp.Primes.P_prime
example : Secp.Primes.IsPrime Secp.Spec.N := Secp.Primes.N_prime

example : ∀ {a : Secp.Spec.F}, a ≠ 0 → a * Secp.Spec.inv a = 1 :=
  @Secp.Spec.mul_inv

example : ∀ (p q : Secp.Spec.Point), Secp.Spec.add p q = Secp.Spec.add q p :=
  Secp.Spec.add_comm

example : ∀ {p : Secp.Spec.Point}, Secp.Spec.OnCurve p → Secp.Spec.add p (Secp.Spec.neg p) = .inf :=
  @Secp.Spec.add_neg_self

example : ∀ {p q r : Secp.Spec.Point},
    Secp.Spec.OnCurve p → Secp.Spec.OnCurve q → Secp.Spec.OnCurve r →
    Secp.Spec.add (Secp.Spec.add p q) r = Secp.Spec.add p (Secp.Spec.add q r) :=
  @Secp.Spec.add_assoc

example : Secp.Spec.smul Secp.Spec.N Secp.Spec.G = .inf :=
  SecpCt.smul_N_G

example : ∀ {d : Nat}, 0 < d → d < Secp.Spec.N → Secp.Spec.smul d Secp.Spec.G ≠ .inf :=
  @SecpCt.smul_G_ne_inf

-- Non-vacuity witness for `smul_G_ne_inf`: `1 · G` satisfies `0 < 1 < N` and is on the curve, not `.inf`
example : 0 < 1 ∧ 1 < Secp.Spec.N ∧ Secp.Spec.smul 1 Secp.Spec.G ≠ .inf :=
  ⟨by decide, by decide, SecpCt.smul_G_ne_inf (by decide) (by decide)⟩

-- Strict BIP 66 DER round-trip completeness and byte canonicality
example : ∀ {sig : ByteArray}, sig.size = 64 → Secp.Ecdsa.parseDer (Secp.Ecdsa.der sig) = some sig :=
  @Secp.Ecdsa.parseDer_der

example : ∀ {b sig : ByteArray}, Secp.Ecdsa.parseDer b = some sig →
    sig.size = 64 ∧ Secp.Ecdsa.der sig = b ∧ 8 ≤ b.size ∧ b.size ≤ 72 :=
  @Secp.Ecdsa.der_parseDer

-- Non-vacuity witness for `parseDer`: concrete 64-byte `(r, s)` encodes to canonical DER and parses back
example : ∃ b sig, sig.size = 64 ∧ Secp.Ecdsa.parseDer b = some sig ∧ Secp.Ecdsa.der sig = b := by
  let sig := Secp.toBE32 1 ++ Secp.toBE32 1
  have hsz : sig.size = 64 := by simp [sig, ByteArray.size_append, SecpCt.toBE32_size]
  exact ⟨Secp.Ecdsa.der sig, sig, hsz, Secp.Ecdsa.parseDer_der hsz, rfl⟩

-- Unconditional BIP 340 & ECDSA signing completeness
example : ∀ {secret message aux sig : ByteArray},
    SecpCt.sign secret message aux = some sig →
    ∃ key, SecpCt.publicKey secret = some key ∧ SecpCt.verify sig message key.1 = true :=
  @SecpCt.verify_sign

example : ∀ (secret message aux : ByteArray),
    SecpCt.signVerified secret message aux = SecpCt.sign secret message aux :=
  SecpCt.signVerified_eq_sign

example : ∀ {secret digest aux sig : ByteArray},
    SecpCt.Ecdsa.sign secret digest aux = some sig →
    ∃ key, SecpCt.publicPoint (SecpCt.Sc.ofBytes secret) = some key ∧
      SecpCt.Ecdsa.verify sig digest key.compressed = true ∧
      Secp.Ecdsa.parseDer (Secp.Ecdsa.der sig) = some sig :=
  @SecpCt.Ecdsa.verify_sign

example : ∀ (secret digest aux : ByteArray),
    SecpCt.Ecdsa.signVerified secret digest aux = SecpCt.Ecdsa.sign secret digest aux :=
  SecpCt.Ecdsa.signVerified_eq_sign

-- Non-vacuity witness for key derivation: secret `1` produces a valid public key
example : ∃ pk parity, SecpCt.publicKey (Secp.toBE32 1) = some (pk, parity) := by
  have hsz : (Secp.toBE32 1).size = 32 := SecpCt.toBE32_size 1
  have hval : Secp.fromBE (Secp.toBE32 1) = 1 := SecpCt.fromBE_toBE32 (by decide)
  obtain ⟨x, y, _, hpk⟩ := SecpCt.publicKey_complete hsz (by omega) (by rw [hval]; decide)
  exact ⟨_, _, hpk⟩

/-! ## `DeviceSync` Stamp Semilattice & Clock Monotonicity -/

example : ∀ (a : Winnow.DeviceSync.Stamp), Winnow.DeviceSync.Stamp.max a a = a :=
  Winnow.Proofs.DeviceSync.Stamp.max_idem

example : ∀ (a b : Winnow.DeviceSync.Stamp),
    Winnow.DeviceSync.Stamp.max a b = Winnow.DeviceSync.Stamp.max b a :=
  Winnow.Proofs.DeviceSync.Stamp.max_comm

example : ∀ (a b c : Winnow.DeviceSync.Stamp),
    Winnow.DeviceSync.Stamp.max (Winnow.DeviceSync.Stamp.max a b) c =
      Winnow.DeviceSync.Stamp.max a (Winnow.DeviceSync.Stamp.max b c) :=
  Winnow.Proofs.DeviceSync.Stamp.max_assoc

example : ∀ (clock now device : Nat) (s : Winnow.DeviceSync.Stamp),
    s.time ≤ clock → s < Winnow.DeviceSync.Stamp.after clock now device :=
  Winnow.Proofs.DeviceSync.Stamp.after_later

end Winnow.Proofs.Gate

#assert_all_axioms Secp SecpCt Winnow WinnowProofs
