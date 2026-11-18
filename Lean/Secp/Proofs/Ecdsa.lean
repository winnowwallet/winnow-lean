import Secp.Proofs.Keys
import Secp.Ecdsa

/-! # ECDSA: what checking a signature means, and what signing returns

`Ecdsa.verify_sound`: when the verifier accepts a signature, the textbook equation holds on the curve as
specified, with `0 < r < N` and `0 < s ≤ N/2`. It assumes, as a hypothesis and not an axiom, that `P` is
prime (`[FieldP]`), as every statement about points here does.

`Ecdsa.sign_verifies`: a signature `sign` returns is one `verify` accepts under the signer's own public key.
Together: a signature this library makes satisfies ECDSA's equation for the key `d·G` (`pubOf_spec`).

`Ecdsa.inverse_eq`: the signer's `1/k` is `k` to the power N − 2 modulo N. A signer written another way (on
machine words, in constant time) that raises to the same power can be proved to return `signRaw`'s
signature from this.

What is not proved: that `signRaw`'s signature is always one `verify` accepts, so that `sign` never fails
for a valid key. That needs the curve's group law (that adding points is associative, and that N times the
generator is the point at infinity) and N to be prime, since `signRaw` divides by raising to the power
N − 2; neither is proved here. So that step is checked each time instead of once: `sign` verifies, with a
verifier that divides by Euclid's algorithm and checks its own answer. -/

namespace Secp
open Spec

namespace Ecdsa

/-! ## The verifier -/

/-- What the verifier divides by `s` with multiplies back to one. -/
theorem inverse?_spec {s w : Nat} (h : inverse? s = some w) : s * w % N = 1 := by
  unfold inverse? at h
  simp only at h
  split at h
  · rename_i checks
    cases h
    exact checks
  · cases h

/-- **Verification is ECDSA's equation on the curve as specified.** When `verify` accepts, the signature is
sixty-four bytes spelling `r` and `s` with `0 < r < N` and `0 < s ≤ N/2`, the key is a point of the curve,
and there is a `w` with `s·w = 1` modulo N for which `(z·w)·G + (r·w)·Q` is a point, not the point at
infinity, whose x modulo N is `r`: for `z` the digest as a number modulo N and `Q` the key. -/
theorem verify_sound [FieldP] {signature digest key : ByteArray}
    (h : verify signature digest key = .ok true) :
    signature.size = 64 ∧ digest.size = 32 ∧
    ∃ qx qy, parseCompressed key = .ok (qx, qy) ∧
      0 < fromBE (signature.extract 0 32) ∧ fromBE (signature.extract 0 32) < N ∧
      0 < fromBE (signature.extract 32 64) ∧ fromBE (signature.extract 32 64) ≤ N / 2 ∧
      ∃ w, fromBE (signature.extract 32 64) * w % N = 1 ∧
        ∃ x y : F,
          Spec.add (Spec.smul (fromBE digest % N * w % N) Spec.G)
            (Spec.smul (fromBE (signature.extract 0 32) * w % N) (.pt qx.toF qy.toF)) = .pt x y
          ∧ x.val % N = fromBE (signature.extract 0 32) := by
  unfold verify at h
  split at h
  · cases h
  · rename_i sizes
    split at h
    · cases h
    · rename_i qx qy parsed
      simp only at h
      split at h
      · cases h
      · rename_i ranges
        split at h
        · cases h
        · rename_i w inverse
          split at h
          · cases h
          · rename_i rQ multiplied
            split at h
            · cases h
            · cases h
            · rename_i x y summed
              simp only [Except.ok.injEq, beq_iff_eq] at h
              refine ⟨by omega, by omega, qx, qy, parsed, by omega, by omega, by omega, by omega, w,
                inverse?_spec inverse, x.toF, y.toF, ?_, h⟩
              have sum := mulGAdd_spec summed
              rw [mulPt_spec multiplied] at sum
              exact sum.symm

/-! ## Signing -/

/-- **A signature `sign` returns verifies** under the signer's own public key, `d·G` compressed. -/
theorem sign_verifies {digest aux signature : ByteArray} {d : Nat} (h : sign digest d aux = .ok signature) :
    ∃ x y, pubOf d = .ok (x, y) ∧ verify signature digest (compressed x y) = .ok true := by
  unfold sign at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i x y key
      split at h
      · rename_i accepted
        cases h
        exact ⟨x, y, key, accepted⟩
      · cases h
      · cases h

/-- What `sign` returns is `signRaw`'s signature, as bytes: the self-check adds nothing and changes nothing. -/
theorem sign_eq_signRaw {digest aux signature : ByteArray} {d : Nat} (h : sign digest d aux = .ok signature) :
    ∃ made, signRaw digest d aux = .ok made ∧ signature = encode made := by
  unfold sign at h
  split at h
  · cases h
  · rename_i made raw
    split at h
    · cases h
    · split at h
      · cases h
        exact ⟨made, raw, rfl⟩
      · cases h
      · cases h

end Ecdsa
end Secp
