import SecpCt.CurveProofs
import SecpCt.BytesProofs
import SecpCt.Schnorr

/-! # The public key, from bytes to bytes

What the pieces add up to: for thirty-two bytes of secret, the two byte strings `publicRaw` returns are the
x and the y of `d · G` in winnow's specification, written the way winnow writes numbers, where `d` is the
number the secret's bytes spell (`publicRaw_spec`). And the bit it returns beside them says whether those
bytes are a key at all: a number from 1 to N − 1 (`Sc.isKey_spec`).

The one assumption is that of `SecpCt/CurveProofs.lean`: that P is prime, as Fermat's little theorem for P.
The theorem is about a secret whose multiple of the generator
is a point and not the point at infinity, which is every key, though that last step (no number from 1 to
N − 1 times G is the point at infinity) is a fact about the curve's order and is not proved here.

Signing is in `SecpCt/SignProofs.lean`. -/

namespace SecpCt
open Secp.Spec (F)
open Secp

/-- A valid element's number is its value in the specification's field. -/
theorem Fe.toNat_of_toF {a : Fe} {x : F} (valid : a.Valid) (h : a.toF = x) : a.toNat = x.val := by
  rw [← h, Fe.toF_val, Nat.mod_eq_of_lt valid]

/-- `isKey` says whether thirty-two bytes are a secret key as they stand: a number from 1 to N − 1. -/
theorem Sc.isKey_spec (b : ByteArray) (h : b.size = 32) :
    Sc.isKey b = if 0 < Secp.fromBE b ∧ Secp.fromBE b < N then 1 else 0 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21,
    b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := bytes32 b h
  rw [fromBE_words]
  simp only [Sc.isKey]
  generalize wordAt _ 24 = u0
  generalize wordAt _ 16 = u1
  generalize wordAt _ 8 = u2
  generalize wordAt _ 0 = u3
  have below := lessN_below u0 u1 u2 u3
  obtain ⟨_, bit⟩ := lessN_spec u0 u1 u2 u3
  have zero := words_zero u0 u1 u2 u3
  rw [nonzero_spec]
  generalize (Sc.lessN u0 u1 u2 u3).2 = flag at *
  generalize value u0 u1 u2 u3 = v at *
  by_cases hz : u0 ||| u1 ||| u2 ||| u3 = 0
  · have : v = 0 := zero.mp hz
    simp only [hz, this, ↓reduceIte, Nat.lt_irrefl, false_and]
    rcases SecpCt.bit_cases flag bit with rfl | rfl <;> rfl
  · have pos : 0 < v := Nat.pos_of_ne_zero (fun e => hz (zero.mpr e))
    simp only [hz, pos, true_and, ↓reduceIte]
    by_cases lt : v < N
    · simp only [lt, ↓reduceIte] at below ⊢
      rcases SecpCt.bit_cases flag bit with rfl | rfl
      · exact absurd below (by decide)
      · rfl
    · simp only [lt, ↓reduceIte] at below ⊢
      rcases SecpCt.bit_cases flag bit with rfl | rfl
      · rfl
      · exact absurd below (by decide)

/-- The public key's two coordinates as `publicRaw` returns them are those of `d · G`, written as winnow
writes numbers, for `d` the number the secret's bytes spell (taken modulo N, which changes nothing for a
key). -/
theorem publicRaw_spec [Fermat] (secret : ByteArray) (h : secret.size = 32) {x y : F}
    (point : Spec.smul (Secp.fromBE secret % N) Spec.G = .pt x y) :
    publicRaw secret = (Secp.toBE32 x.val, Secp.toBE32 y.val, Sc.isKey secret) := by
  have rep := mulGenerator_rep (Sc.ofBytes secret)
  rw [Sc.ofBytes_spec secret h, point] at rep
  obtain ⟨hx, hy, _, vx, vy⟩ := affine_point rep
  simp only [publicRaw, Fe.bytes_spec, Fe.toNat_of_toF vx hx, Fe.toNat_of_toF vy hy]

end SecpCt
