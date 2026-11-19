import Secp.Gate
import SecpCt.Word
import SecpCt.Field
import SecpCt.Scalar
import SecpCt.Point
import SecpCt.Schnorr
import SecpCt.Ecdsa
import SecpCt.Keys
import SecpCt.Proofs
import SecpCt.ScalarProofs
import SecpCt.ScalarMulProofs
import SecpCt.CurveProofs
import SecpCt.BytesProofs
import SecpCt.KeyProofs
import SecpCt.SignProofs
import SecpCt.EcdsaProofs
import SecpCt.KeySpecs
import SecpCt.CompleteProofs

/-! # The gate for `SecpCt`: what it computes is what the specification says

Imported by the library root, so `lake build` fails if any of these depends on a `sorry` or on any axiom
beyond the standard three (`propext`, `Quot.sound`, `Classical.choice`). Primality of `P` and `N`, the
curve's abelian group law, and generator order `N` are proved unconditionally. No proof here uses
`bv_decide` or `native_decide`, which would each add an axiom the gate refuses. -/

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
-- keys and BIP 340: the public key is the specification's, the signature the reference's (`Secp.Bip340.signWith`)
#assert_axioms SecpCt.publicKey_spec
#assert_axioms SecpCt.addRaw_spec
#assert_axioms SecpCt.signRaw_eq
#assert_axioms SecpCt.sign_eq
-- ECDSA: the signature is the reference's (`Secp.Ecdsa.signWith`)
#assert_axioms SecpCt.Ecdsa.signRaw_eq
#assert_axioms SecpCt.Ecdsa.sign_eq
-- the curve: multiplying any point of it, doubling, and reading a result off, are the specification's
#assert_axioms SecpCt.rep_add
#assert_axioms SecpCt.rep_double
#assert_axioms SecpCt.mul_rep
#assert_axioms SecpCt.mulPublic_rep
#assert_axioms SecpCt.affine_spec
-- generator order N and prime-order subgroup algebra
#assert_axioms SecpCt.smul_N_G
#assert_axioms SecpCt.nsmul_mod_N
#assert_axioms SecpCt.smul_G_ne_inf
#assert_axioms SecpCt.smul_neg_G
-- public keys: soundness and lossless round-trip completeness
#assert_axioms SecpCt.Fe.sqrt?_complete
#assert_axioms SecpCt.liftX?_spec
#assert_axioms SecpCt.liftX?_complete
#assert_axioms SecpCt.parseXOnly_spec
#assert_axioms SecpCt.parseXOnly_xBytes
#assert_axioms SecpCt.parseCompressed_spec
#assert_axioms SecpCt.parseCompressed_compressed
#assert_axioms SecpCt.parseUncompressed_spec
#assert_axioms SecpCt.scalar?_spec
-- tweaks: the specification's sums and products
#assert_axioms SecpCt.generatorMul_spec
#assert_axioms SecpCt.publicPoint_spec
#assert_axioms SecpCt.publicPoint_complete
#assert_axioms SecpCt.pointAdd_spec
#assert_axioms SecpCt.pointMul_spec
#assert_axioms SecpCt.combine_spec
#assert_axioms SecpCt.evenKey_spec
-- verification and signing completeness: accepted iff curve equation holds, and `sign` always verifies
#assert_axioms SecpCt.verify_sound
#assert_axioms SecpCt.verify_sign
#assert_axioms SecpCt.signVerified_verifies
#assert_axioms SecpCt.signVerified_eq_sign
#assert_axioms SecpCt.Ecdsa.verify_sound
#assert_axioms SecpCt.Ecdsa.verify_sign
#assert_axioms SecpCt.Ecdsa.signVerified_verifies
#assert_axioms SecpCt.Ecdsa.signVerified_eq_sign

#assert_all_axioms SecpCt
