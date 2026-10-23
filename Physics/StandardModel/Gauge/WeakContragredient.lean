import Physics.StandardModel.Gauge.Tensors.WeakContragredient
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.WeakContragredient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMEpsilonTensor.eps2Bilin.eq_1 => Physics.SMEpsilonTensor.eps2Bilin.eq_1,
  GUT.StandardSMContragredient.chargedWeakDualEquiv => Physics.StandardSMContragredient.chargedWeakDualEquiv,
  GUT.StandardSMContragredient.eps2Bilin_injective => Physics.StandardSMContragredient.eps2Bilin_injective,
  GUT.StandardSMContragredient.eps2_charged_invariant => Physics.StandardSMContragredient.eps2_charged_invariant,
  GUT.StandardSMContragredient.eps2_twist_invariant => Physics.StandardSMContragredient.eps2_twist_invariant,
  GUT.StandardSMContragredient.leptonDualEquiv => Physics.StandardSMContragredient.leptonDualEquiv,
  GUT.StandardSMContragredient.weakDualLinearEquiv => Physics.StandardSMContragredient.weakDualLinearEquiv,
  GUT.StandardSMContragredient.weakDualLinearEquiv.eq_1 => Physics.StandardSMContragredient.weakDualLinearEquiv.eq_1,
  GUT.StandardSMContragredient.weakDualLinearEquiv_symm_apply => Physics.StandardSMContragredient.weakDualLinearEquiv_symm_apply
]

assert_compatible GUT.SMEpsilonTensor.eps2Bilin.eq_1 => Physics.SMEpsilonTensor.eps2Bilin.eq_1
assert_compatible GUT.StandardSMContragredient.chargedWeakDualEquiv => Physics.StandardSMContragredient.chargedWeakDualEquiv
assert_compatible GUT.StandardSMContragredient.eps2Bilin_injective => Physics.StandardSMContragredient.eps2Bilin_injective
assert_compatible GUT.StandardSMContragredient.eps2_charged_invariant => Physics.StandardSMContragredient.eps2_charged_invariant
assert_compatible GUT.StandardSMContragredient.eps2_twist_invariant => Physics.StandardSMContragredient.eps2_twist_invariant
assert_compatible GUT.StandardSMContragredient.leptonDualEquiv => Physics.StandardSMContragredient.leptonDualEquiv
assert_compatible GUT.StandardSMContragredient.weakDualLinearEquiv => Physics.StandardSMContragredient.weakDualLinearEquiv
assert_compatible GUT.StandardSMContragredient.weakDualLinearEquiv.eq_1 => Physics.StandardSMContragredient.weakDualLinearEquiv.eq_1
assert_compatible GUT.StandardSMContragredient.weakDualLinearEquiv_symm_apply => Physics.StandardSMContragredient.weakDualLinearEquiv_symm_apply
