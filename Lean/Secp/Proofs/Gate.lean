import Secp.Gate
import Secp.Curve.Spec
import Secp.Signing
import Secp.Bytes
import Secp.Sha256
import Secp.Der
import Secp.Proofs.Primes
import Secp.Proofs.Group
import Secp.Proofs.Der

/-! # The gate for `Secp`: the specification's own theorems, then everything under `Secp`

`Secp` is what the curve code is proved against and the plain pieces around it: the curve as specified
(`Secp/Curve/Spec.lean`), signing as BIP 340 and ECDSA give it (`Secp/Signing.lean`), bytes, SHA-256 and
DER. Primality of both `P` and `N`, the curve's abelian group law, and strict BIP 66 DER canonicality are
proved unconditionally in `Secp/Proofs/`.

Imported by the library root, so `lake build` fails if any of these depends on a `sorry` or on any axiom
beyond the standard three. -/

-- P and N are prime (Pocklington certificates), discharging Fermat's little theorem and field inverses
#assert_axioms Secp.Primes.P_prime
#assert_axioms Secp.Primes.N_prime
#assert_axioms Secp.Primes.fermat_P
#assert_axioms Secp.Primes.fermat_N
#assert_axioms Secp.Spec.mul_inv
#assert_axioms Secp.Spec.onCurve_y_ne_zero

-- the curve as specified forms an abelian group, and 256-bit `smul` equals Peano `nsmul`
#assert_axioms Secp.Spec.G_onCurve
#assert_axioms Secp.Spec.add_onCurve
#assert_axioms Secp.Spec.smul_onCurve
#assert_axioms Secp.Spec.add_comm
#assert_axioms Secp.Spec.add_neg_self
#assert_axioms Secp.Spec.add_assoc
#assert_axioms Secp.Spec.nsmul_add
#assert_axioms Secp.Spec.nsmul_mul
#assert_axioms Secp.Spec.smul_eq_nsmul

-- ECDSA's division is the power N − 2, and is an exact inverse modulo N
#assert_axioms Secp.Ecdsa.inverse_eq
#assert_axioms Secp.Ecdsa.mul_inverse

-- strict BIP 66 DER round-trip and byte canonicality
#assert_axioms Secp.Ecdsa.der_size_bounds
#assert_axioms Secp.Ecdsa.parseDer_der
#assert_axioms Secp.Ecdsa.der_parseDer

#assert_all_axioms Secp
