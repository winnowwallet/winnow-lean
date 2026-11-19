import Secp.Proofs.Gate
import SecpCt.Gate
import Winnow
import Winnow.Proofs.DeviceSyncProofs
import Winnow.Proofs.Custody

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

/-! ## Phase 2: the key behind every address the wallet shows can sign for it

What "can sign for" means is `Winnow.Spec.Custody.KeyPathSpendable`: the script is `OP_1` and the x of the
key's point, every signature the wallet makes with the key verifies under it by the wallet's own BIP 340
check (`SecpCt.verify`, itself held to the curve by `SecpCt.verify_sound`), and signing succeeds for any
message short of BIP 340's zero nonce. It is not a statement about Bitcoin Core's verifier. -/

section custody
open Winnow.Keys Winnow.Spec.Custody Winnow.Proofs.Custody

-- Tweaking a public key is tweaking the secret key: the same point or the same refusal, for any bytes
example : ∀ {d : Secret} {p : Point}, d.Valid → pointOfSecret d = .ok p → ∀ (tw : ByteArray),
    publicAdd p tw = (privateAdd d tw >>= pointOfSecret) :=
  @publicAdd_eq_privateAdd

example : ∀ {d : Secret} {p : Point}, d.Valid → pointOfSecret d = .ok p → ∀ (tw : ByteArray),
    xonlyAdd (xonlyBytes p) tw =
      (do let d' ← keypairXonlyAdd d tw; return xonlyOf (← pointOfSecret d')) :=
  @xonlyAdd_eq_keypairXonlyAdd

-- The hypotheses hold of a key: the number 1 is one, and it has a point
example : ∃ (d : Secret) (p : Point), d.Valid ∧ pointOfSecret d = .ok p := by
  have hsz : (Secp.toBE32 1).size = 32 := SecpCt.toBE32_size 1
  have hval : Secp.fromBE (Secp.toBE32 1) = 1 := SecpCt.fromBE_toBE32 (by decide)
  have hvis : isValidSecret (Secp.toBE32 1) = true :=
    (isValidSecret_iff _).mpr ⟨hsz, by rw [hval]; decide, by rw [hval]; decide⟩
  obtain ⟨d, _, hd, _⟩ := secretOf_of_isValidSecret hvis
  obtain ⟨p, hp, _, _⟩ := pointOfSecret_complete hd
  exact ⟨d, p, hd, hp⟩

-- A key signs for the script locked to it
example : ∀ {secret : ByteArray} {d : Secret} {p : Point},
    secretOf secret = .ok d → pointOfSecret d = .ok p →
    KeyPathSpendable secret (p2trScript (xonlyBytes p)) :=
  @keyPathSpendable_of_secret

example : ∃ secret spk, KeyPathSpendable secret spk := by
  have hsz : (Secp.toBE32 1).size = 32 := SecpCt.toBE32_size 1
  have hval : Secp.fromBE (Secp.toBE32 1) = 1 := SecpCt.fromBE_toBE32 (by decide)
  have hvis : isValidSecret (Secp.toBE32 1) = true :=
    (isValidSecret_iff _).mpr ⟨hsz, by rw [hval]; decide, by rw [hval]; decide⟩
  obtain ⟨d, hsec, hd, _⟩ := secretOf_of_isValidSecret hvis
  obtain ⟨p, hp, _, _⟩ := pointOfSecret_complete hd
  exact ⟨_, _, keyPathSpendable_of_secret hsec hp⟩

-- BIP 32: a watch-only key derives what the signing key derives, at every index that is not hardened
example : ∀ {k : HDKey} {index : UInt32}, WellFormedPrivateHDKey k → index < HDKey.hardenedOffset →
    (k.child index).map HDKey.neutered = k.neutered.child index :=
  @HDKey.child_neutered_comm

example : ∀ {k : HDKey} {chain index : UInt32}, WellFormedPrivateHDKey k →
    chain < HDKey.hardenedOffset → index < HDKey.hardenedOffset →
    (k.child chain >>= fun c => c.child index).map HDKey.neutered =
      (k.neutered.child chain >>= fun c => c.child index) :=
  @HDKey.child2_neutered_comm

example : ∀ {k ck : HDKey} {index : UInt32}, WellFormedPrivateHDKey k → k.child index = .ok ck →
    WellFormedPrivateHDKey ck :=
  @HDKey.child_preserves_wellFormed

-- Taproot: the key behind an output spends it by its key path, with a script tree or without
example : ∀ {d : Secret} {p : Point} {merkleRoot : Option ByteArray} {spk : ByteArray},
    d.Valid → pointOfSecret d = .ok p →
    Taproot.scriptPubKey (xonlyBytes p) merkleRoot = .ok spk →
    ∃ d' p', keypairXonlyAdd d (Taproot.tweak (xonlyBytes p) merkleRoot) = .ok d' ∧ d'.Valid ∧
      pointOfSecret d' = .ok p' ∧
      xonlyAdd (xonlyBytes p) (Taproot.tweak (xonlyBytes p) merkleRoot) = .ok (xonlyOf p') ∧
      spk = p2trScript (xonlyBytes p') ∧
      KeyPathSpendable d'.bytes spk :=
  @Taproot.keyPath_spendable

-- BIP 86: an address the wallet shows from its public keys is one its private keys sign for
example : ∀ {account pubKey : HDKey} {chain index : UInt32} {spk : ByteArray},
    WellFormedPrivateHDKey account →
    chain < HDKey.hardenedOffset → index < HDKey.hardenedOffset →
    (account.neutered.child chain >>= fun c => c.child index) = .ok pubKey →
    Taproot.scriptPubKey (BIP86.xonlyPublicKey pubKey) none = .ok spk →
    ∃ privKey sk tweakedSk,
      (account.child chain >>= fun c => c.child index) = .ok privKey ∧
      privKey.neutered = pubKey ∧
      privKey.privateKey = some sk ∧
      BIP86.tweakedPrivateKey sk = .ok tweakedSk ∧
      BIP86.tweakedOutputKey (BIP86.xonlyPublicKey pubKey) = .ok (spk.extract 2 34) ∧
      KeyPathSpendable tweakedSk spk :=
  @BIP86.tweakedPrivateKey_spendable

-- Script trees: the branch hash does not depend on the order of its two children, and every control block
-- the wallet makes commits its leaf into the output
example : ∀ (a b : ByteArray), Taproot.branchHash a b = Taproot.branchHash b a :=
  Winnow.Proofs.Custody.Taproot.branchHash_comm

example : ∀ {internalKey : ByteArray} {tree : Taproot.Tree} {cbs : List Taproot.ControlBlock},
    Taproot.controlBlocks internalKey tree = .ok cbs →
    ∃ spk,
      Taproot.scriptPubKey internalKey (some (Taproot.merkleRoot tree)) = .ok spk ∧
      cbs.length = (Taproot.hashes tree).2.length ∧
      ∀ (j : Nat) (hj1 : j < cbs.length) (hj2 : j < (Taproot.hashes tree).2.length),
        ValidScriptPathCommitment (cbs[j]'hj1) ((Taproot.hashes tree).2[j]'hj2).1
          ((Taproot.hashes tree).2[j]'hj2).2.1 spk :=
  @Winnow.Proofs.Custody.Taproot.controlBlocks_valid

-- A card for one person: the secret the wallet derives for a payment signs for the script the payer derives
example : ∀ {spend : ByteArray} {label : Option ByteArray} {b d : Secret} {B : Point}
    {code : CardCode} {i : UInt32} {spk : ByteArray},
    secretOf spend = .ok b → CardKey b label d → pointOfSecret d = .ok B →
    serializeCompressed B = code.spendKey →
    SilentPaymentPairing.codeScript code i = .ok spk →
    ∃ sk, SilentPaymentPairing.codeSpendSecret spend label code i = .ok sk ∧ KeyPathSpendable sk spk :=
  @Winnow.Proofs.Custody.SilentPaymentPairing.codeSpendSecret_spendable

example : ∀ {scan spend : ByteArray} {hrp : String} {k i : UInt32} {code : CardCode} {spk : ByteArray},
    SilentPaymentPairing.codeFor scan spend hrp k = .ok code →
    SilentPaymentPairing.codeScript code i = .ok spk →
    ∃ label sk,
      SilentPaymentPairing.labelFor scan k = .ok label ∧
      SilentPaymentPairing.codeSpendSecret spend (some label) code i = .ok sk ∧
      KeyPathSpendable sk spk :=
  @Winnow.Proofs.Custody.SilentPaymentPairing.codeFor_spendable

example : ∀ {master : HDKey} {coinType k i : UInt32} {hrp : String}
    {scan spend : ByteArray} {card : PairingCard} {spk : ByteArray},
    SilentPaymentPairing.keys master coinType = .ok (scan, spend) →
    SilentPaymentPairing.issue master coinType hrp k = .ok card →
    SilentPaymentPairing.scriptPubKey card i = .ok spk →
    ∃ sk, SilentPaymentPairing.spendSecret spend card i = .ok sk ∧ KeyPathSpendable sk spk :=
  @Winnow.Proofs.Custody.SilentPaymentPairing.issue_spendable

end custody

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
