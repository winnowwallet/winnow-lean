import Secp.Gate
import Secp.Curve.Spec
import Secp.Signing
import Secp.Bytes
import Secp.Sha256
import Secp.Der

/-! # The gate for `Secp`: the specification's own theorems, then everything under `Secp`

`Secp` is what the curve code is proved against and the plain pieces around it: the curve as specified
(`Secp/Curve/Spec.lean`), signing as BIP 340 and ECDSA give it (`Secp/Signing.lean`), bytes, SHA-256 and
DER. The arithmetic that runs, and the proofs that it is this, are `SecpCt` (`SecpCt/Gate.lean`).

Imported by the library root, so `lake build` fails if any of these depends on a `sorry` or on any axiom
beyond the standard three. -/

-- the curve as specified: the generator is on it, and sums and multiples of its points are
#assert_axioms Secp.Spec.G_onCurve
#assert_axioms Secp.Spec.add_onCurve
#assert_axioms Secp.Spec.smul_onCurve
-- ECDSA's division, as the reference writes it, is the power N − 2
#assert_axioms Secp.Ecdsa.inverse_eq

#assert_all_axioms Secp
