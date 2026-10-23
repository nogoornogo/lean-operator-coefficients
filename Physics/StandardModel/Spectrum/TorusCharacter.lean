import Physics.StandardModel.Spectrum.Representations.TorusCharacter
import Physics.StandardModel.Spectrum.SMChiralIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.TorusCharacter instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SU5.TorusCharacter.CombinedGroup => Physics.SU5.TorusCharacter.CombinedGroup,
  GUT.SU5.TorusCharacter.eval => Physics.SU5.TorusCharacter.eval,
  GUT.SU5.TorusCharacter.eval.eq_1 => Physics.SU5.TorusCharacter.eval.eq_1,
  GUT.SU5.TorusCharacter.evalAddHom => Physics.SU5.TorusCharacter.evalAddHom,
  GUT.SU5.TorusCharacter.evalAddHom_apply => Physics.SU5.TorusCharacter.evalAddHom_apply,
  GUT.SU5.TorusCharacter.eval_chiralDifference => Physics.SU5.TorusCharacter.eval_chiralDifference,
  GUT.SU5.TorusCharacter.eval_dual => Physics.SU5.TorusCharacter.eval_dual,
  GUT.SU5.TorusCharacter.eval_injective => Physics.SU5.TorusCharacter.eval_injective,
  GUT.SU5.TorusCharacter.eval_lift => Physics.SU5.TorusCharacter.eval_lift,
  GUT.SU5.TorusCharacter.eval_permute => Physics.SU5.TorusCharacter.eval_permute,
  GUT.SU5.TorusCharacter.eval_single => Physics.SU5.TorusCharacter.eval_single,
  GUT.SU5.TorusCharacter.keyCharacter => Physics.SU5.TorusCharacter.keyCharacter,
  GUT.SU5.TorusCharacter.keyCharacter_apply => Physics.SU5.TorusCharacter.keyCharacter_apply,
  GUT.SU5.TorusCharacter.keyCharacter_injective => Physics.SU5.TorusCharacter.keyCharacter_injective,
  GUT.SU5.TorusCharacter.keyCharacter_neg => Physics.SU5.TorusCharacter.keyCharacter_neg,
  GUT.SU5.TorusCharacter.lift => Physics.SU5.TorusCharacter.lift,
  GUT.SU5.TorusCharacter.lift.eq_1 => Physics.SU5.TorusCharacter.lift.eq_1,
  GUT.SU5.TorusCharacter.rawCharacter => Physics.SU5.TorusCharacter.rawCharacter,
  GUT.SU5.TorusCharacter.rawCharacter.eq_1 => Physics.SU5.TorusCharacter.rawCharacter.eq_1,
  GUT.SU5.TorusCharacter.weightCharacter => Physics.SU5.TorusCharacter.weightCharacter,
  GUT.SU5.TorusCharacter.weightCharacter_coordinates => Physics.SU5.TorusCharacter.weightCharacter_coordinates,
  GUT.SU5.TorusCharacter.weightCharacter_injective => Physics.SU5.TorusCharacter.weightCharacter_injective,
  GUT.SU5.TorusCharacter.weightCharacter_normalize => Physics.SU5.TorusCharacter.weightCharacter_normalize,
  GUT.SU5.TorusCharacter.weightCharacter_permute => Physics.SU5.TorusCharacter.weightCharacter_permute
]

assert_compatible GUT.SU5.TorusCharacter.CombinedGroup => Physics.SU5.TorusCharacter.CombinedGroup
assert_compatible GUT.SU5.TorusCharacter.eval => Physics.SU5.TorusCharacter.eval
assert_compatible GUT.SU5.TorusCharacter.eval.eq_1 => Physics.SU5.TorusCharacter.eval.eq_1
assert_compatible GUT.SU5.TorusCharacter.evalAddHom => Physics.SU5.TorusCharacter.evalAddHom
assert_compatible GUT.SU5.TorusCharacter.evalAddHom_apply => Physics.SU5.TorusCharacter.evalAddHom_apply
assert_compatible GUT.SU5.TorusCharacter.eval_chiralDifference => Physics.SU5.TorusCharacter.eval_chiralDifference
assert_compatible GUT.SU5.TorusCharacter.eval_dual => Physics.SU5.TorusCharacter.eval_dual
assert_compatible GUT.SU5.TorusCharacter.eval_injective => Physics.SU5.TorusCharacter.eval_injective
assert_compatible GUT.SU5.TorusCharacter.eval_lift => Physics.SU5.TorusCharacter.eval_lift
assert_compatible GUT.SU5.TorusCharacter.eval_permute => Physics.SU5.TorusCharacter.eval_permute
assert_compatible GUT.SU5.TorusCharacter.eval_single => Physics.SU5.TorusCharacter.eval_single
assert_compatible GUT.SU5.TorusCharacter.keyCharacter => Physics.SU5.TorusCharacter.keyCharacter
assert_compatible GUT.SU5.TorusCharacter.keyCharacter_apply => Physics.SU5.TorusCharacter.keyCharacter_apply
assert_compatible GUT.SU5.TorusCharacter.keyCharacter_injective => Physics.SU5.TorusCharacter.keyCharacter_injective
assert_compatible GUT.SU5.TorusCharacter.keyCharacter_neg => Physics.SU5.TorusCharacter.keyCharacter_neg
assert_compatible GUT.SU5.TorusCharacter.lift => Physics.SU5.TorusCharacter.lift
assert_compatible GUT.SU5.TorusCharacter.lift.eq_1 => Physics.SU5.TorusCharacter.lift.eq_1
assert_compatible GUT.SU5.TorusCharacter.rawCharacter => Physics.SU5.TorusCharacter.rawCharacter
assert_compatible GUT.SU5.TorusCharacter.rawCharacter.eq_1 => Physics.SU5.TorusCharacter.rawCharacter.eq_1
assert_compatible GUT.SU5.TorusCharacter.weightCharacter => Physics.SU5.TorusCharacter.weightCharacter
assert_compatible GUT.SU5.TorusCharacter.weightCharacter_coordinates => Physics.SU5.TorusCharacter.weightCharacter_coordinates
assert_compatible GUT.SU5.TorusCharacter.weightCharacter_injective => Physics.SU5.TorusCharacter.weightCharacter_injective
assert_compatible GUT.SU5.TorusCharacter.weightCharacter_normalize => Physics.SU5.TorusCharacter.weightCharacter_normalize
assert_compatible GUT.SU5.TorusCharacter.weightCharacter_permute => Physics.SU5.TorusCharacter.weightCharacter_permute
