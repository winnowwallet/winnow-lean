import Secp.Gate
import Secp.Proofs.Keys

/-! # The gate: every advertised theorem, then everything under `Secp`

Imported by the library root, so `lake build` fails if any of these depends on a `sorry` or on
any axiom beyond the standard three. -/

-- the limb primitives and multi-limb arithmetic
#assert_axioms Secp.mulWide_spec
#assert_axioms Secp.adc_spec
#assert_axioms Secp.sbb_spec
#assert_axioms Secp.addc_spec
#assert_axioms Secp.subb_spec
#assert_axioms Secp.mulAddRow_spec
#assert_axioms Secp.mulL_spec
-- the field: limbs below P are the integers modulo P
#assert_axioms Secp.reduce_spec
#assert_axioms Secp.Fq.toF_add
#assert_axioms Secp.Fq.toF_sub
#assert_axioms Secp.Fq.toF_mul
#assert_axioms Secp.Fq.toF_neg
#assert_axioms Secp.Fq.toF_inj
#assert_axioms Secp.Fq.inv?_spec
#assert_axioms Secp.Fq.sqrt?_spec
-- the spec curve
#assert_axioms Secp.Spec.G_onCurve
#assert_axioms Secp.Spec.add_onCurve
#assert_axioms Secp.Spec.smul_onCurve
-- Jacobian formulas and scalar multiplication
#assert_axioms Secp.dblF_correct
#assert_axioms Secp.maddF_correct
#assert_axioms Secp.rep_double
#assert_axioms Secp.rep_add
#assert_axioms Secp.smul?_spec
-- keys, tweaks and BIP340
#assert_axioms Secp.pubOf_spec
#assert_axioms Secp.pubOf_onCurve
#assert_axioms Secp.liftX?_spec
#assert_axioms Secp.parseCompressed_spec
#assert_axioms Secp.tweak_spec
#assert_axioms Secp.secretAdd_spec
#assert_axioms Secp.secretAddXOnly_spec
#assert_axioms Secp.pointAdd_spec
#assert_axioms Secp.xonlyAdd_spec
#assert_axioms Secp.verify_sound
#assert_axioms Secp.signRaw_key
#assert_axioms Secp.sign_verifies

#assert_all_axioms Secp
