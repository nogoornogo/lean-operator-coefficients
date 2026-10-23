import Physics.StandardModel.Spectrum.Representations.SMChiralIndex
import Physics.StandardModel.Spectrum.FiniteSMTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.SMChiralIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StandardWeylDualTarget.chiralDifference => Physics.StandardWeylDualTarget.chiralDifference,
  GUT.StandardWeylDualTarget.chiralDifference.eq_1 => Physics.StandardWeylDualTarget.chiralDifference.eq_1,
  GUT.StandardWeylDualTarget.chiralDifference_apply_selfDual => Physics.StandardWeylDualTarget.chiralDifference_apply_selfDual,
  GUT.StandardWeylDualTarget.chiralDifference_isWeylInvariant => Physics.StandardWeylDualTarget.chiralDifference_isWeylInvariant,
  GUT.StandardWeylDualTarget.dualCharacter => Physics.StandardWeylDualTarget.dualCharacter,
  GUT.StandardWeylDualTarget.dualCharacter.eq_1 => Physics.StandardWeylDualTarget.dualCharacter.eq_1,
  GUT.StandardWeylDualTarget.dualCharacter_apply => Physics.StandardWeylDualTarget.dualCharacter_apply,
  GUT.StandardWeylDualTarget.dualCharacter_dualCharacter => Physics.StandardWeylDualTarget.dualCharacter_dualCharacter,
  GUT.StandardWeylDualTarget.permuteKey_neg => Physics.StandardWeylDualTarget.permuteKey_neg,
  GUT.StandardWeylDualTarget.permuteResolved_dualCharacter => Physics.StandardWeylDualTarget.permuteResolved_dualCharacter,
  GUT.StandardWeylDualTarget.smReducedWeight_ne_neg => Physics.StandardWeylDualTarget.smReducedWeight_ne_neg
]

assert_compatible GUT.StandardWeylDualTarget.chiralDifference => Physics.StandardWeylDualTarget.chiralDifference
assert_compatible GUT.StandardWeylDualTarget.chiralDifference.eq_1 => Physics.StandardWeylDualTarget.chiralDifference.eq_1
assert_compatible GUT.StandardWeylDualTarget.chiralDifference_apply_selfDual => Physics.StandardWeylDualTarget.chiralDifference_apply_selfDual
assert_compatible GUT.StandardWeylDualTarget.chiralDifference_isWeylInvariant => Physics.StandardWeylDualTarget.chiralDifference_isWeylInvariant
assert_compatible GUT.StandardWeylDualTarget.dualCharacter => Physics.StandardWeylDualTarget.dualCharacter
assert_compatible GUT.StandardWeylDualTarget.dualCharacter.eq_1 => Physics.StandardWeylDualTarget.dualCharacter.eq_1
assert_compatible GUT.StandardWeylDualTarget.dualCharacter_apply => Physics.StandardWeylDualTarget.dualCharacter_apply
assert_compatible GUT.StandardWeylDualTarget.dualCharacter_dualCharacter => Physics.StandardWeylDualTarget.dualCharacter_dualCharacter
assert_compatible GUT.StandardWeylDualTarget.permuteKey_neg => Physics.StandardWeylDualTarget.permuteKey_neg
assert_compatible GUT.StandardWeylDualTarget.permuteResolved_dualCharacter => Physics.StandardWeylDualTarget.permuteResolved_dualCharacter
assert_compatible GUT.StandardWeylDualTarget.smReducedWeight_ne_neg => Physics.StandardWeylDualTarget.smReducedWeight_ne_neg
