import Secp.Signing
import Winnow.Keys.BIP86
import Winnow.Keys.Taproot
import Winnow.Keys.SilentPaymentPairing

/-! # Pure Custody & Spendability Specifications (`Winnow.Spec.Custody`)

Relational specifications for key tweaking, BIP 32 watch/sign derivation agreement, BIP 86 / BIP 341
Taproot key-path and script-path spendability, and per-person Card (`#94`) spendability.
Contains zero theorems (enforced by `scripts/check-proofs`). -/

namespace Winnow.Spec.Custody

open Winnow.Keys

/-- A private `HDKey` whose `publicKey` is the compressed curve point of its 32-byte `privateKey`. -/
def WellFormedPrivateHDKey (k : HDKey) : Prop :=
  ∃ sk, k.privateKey = some sk ∧ publicKeyOf sk = .ok k.publicKey

/-- Standard 34-byte P2TR witness-v1 locking script `OP_1 <32-byte x-only output key>`. -/
def p2trScript (outputKey : ByteArray) : ByteArray :=
  ByteArray.mk #[0x51, 0x20] ++ outputKey

/-- Deterministic BIP 340 nonce scalar `k₀ ∈ [0, N)` for signing `msg` with even-adjusted 32-byte key
`evenSecret` and x-only public key `outputKey`. -/
def bip340Nonce (evenSecret outputKey msg aux : ByteArray) : Nat :=
  let t := Secp.xorBytes evenSecret (Secp.Sha256.tagged "BIP0340/aux" aux)
  Secp.hashMod (Secp.Sha256.tagged "BIP0340/nonce" (t ++ outputKey ++ msg))

/-- `secret` validly spends `scriptPubKey` via Taproot key-path:
1. `secret` is a valid curve secret `d` (`1 ≤ d < N`) with public curve point `p = d · G`;
2. `scriptPubKey` is `OP_1 <xonlyBytes p>` (`34` bytes, `32`-byte witness program);
3. Every signature returned by `schnorrSign d msg aux` verifies under `schnorrVerify (xonlyBytes p) msg sig = .ok true`;
4. `schnorrSign d msg aux` succeeds whenever `aux.size = 32` and the BIP 340 deterministic nonce is non-zero. -/
def KeyPathSpendable (secret scriptPubKey : ByteArray) : Prop :=
  ∃ d p,
    secretOf secret = .ok d ∧
    pointOfSecret d = .ok p ∧
    (xonlyBytes p).size = 32 ∧
    scriptPubKey = p2trScript (xonlyBytes p) ∧
    (∀ msg aux sig, schnorrSign d msg aux = .ok sig → schnorrVerify (xonlyBytes p) msg sig = .ok true) ∧
    (∀ msg aux, aux.size = 32 →
      bip340Nonce (SecpCt.evenKey d.scalar).bytes (xonlyBytes p) msg aux ≠ 0 →
      ∃ sig, schnorrSign d msg aux = .ok sig ∧ schnorrVerify (xonlyBytes p) msg sig = .ok true)

/-- BIP 341 verifier reconstruction of the Taproot Merkle root from a leaf script and control-block path. -/
def reconstructMerkleRoot (leafVersion : UInt8) (script : ByteArray) (path : List ByteArray) : ByteArray :=
  path.foldl Taproot.branchHash (Taproot.leafHash leafVersion script)

/-- A BIP 341 control block `cb` validly commits `(leafVersion, script)` into `scriptPubKey`. -/
def ValidScriptPathCommitment (cb : Taproot.ControlBlock) (leafVersion : UInt8) (script : ByteArray)
    (scriptPubKey : ByteArray) : Prop :=
  cb.leafVersion = leafVersion ∧
  ∃ outputKey,
    outputKey.size = 32 ∧
    scriptPubKey = p2trScript outputKey ∧
    Taproot.tweakedOutputKey cb.internalKey (some (reconstructMerkleRoot cb.leafVersion script cb.path)) =
      .ok (outputKey, cb.outputKeyParity)

/-- The key a card's spend key is the point of: the wallet's spend key `b` itself (a 0.9.12 card), or `b`
with the person's label added (a code). -/
def CardKey (b : Secret) (label : Option ByteArray) (d : Secret) : Prop :=
  match label with
  | none => d = b
  | some l => privateAdd b l = .ok d

end Winnow.Spec.Custody
