import Secp.Gate
import SecpCt.Word
import SecpCt.Field
import SecpCt.Scalar
import SecpCt.Point
import SecpCt.Schnorr
import SecpCt.Ecdsa
import SecpCt.Proofs
import SecpCt.ScalarProofs
import SecpCt.ScalarMulProofs
import SecpCt.CurveProofs
import SecpCt.BytesProofs
import SecpCt.KeyProofs
import SecpCt.SignProofs
import SecpCt.EcdsaProofs

/-! # The gate for `SecpCt`: what it returns is what the reference returns

Imported by the library root, so `lake build` fails if any of these depends on a `sorry` or on any axiom
beyond the standard three. That P is prime is a hypothesis of the theorems that need it (`[Fermat]`), never an
axiom. No proof here uses `bv_decide` or `native_decide`, which would each add an axiom the gate refuses. -/

-- the field and the scalars: each operation is the arithmetic modulo P, or modulo N
#assert_axioms SecpCt.add_spec
#assert_axioms SecpCt.sub_spec
#assert_axioms SecpCt.neg_spec
#assert_axioms SecpCt.mul_spec
#assert_axioms SecpCt.canon_spec
#assert_axioms SecpCt.inv_spec
#assert_axioms SecpCt.Sc.add_spec
#assert_axioms SecpCt.Sc.neg_spec
#assert_axioms SecpCt.Sc.mul_spec
#assert_axioms SecpCt.Sc.inv_spec
#assert_axioms SecpCt.Sc.isHigh_spec
-- keys and BIP 340: the public key and the signature are the reference's
#assert_axioms SecpCt.publicKey_spec
#assert_axioms SecpCt.addRaw_spec
#assert_axioms SecpCt.signRaw_eq
#assert_axioms SecpCt.sign_eq
-- ECDSA: the signature is the reference's (`Secp.Ecdsa.signRaw`)
#assert_axioms SecpCt.Ecdsa.signRaw_eq
#assert_axioms SecpCt.Ecdsa.sign_eq

#assert_all_axioms SecpCt
