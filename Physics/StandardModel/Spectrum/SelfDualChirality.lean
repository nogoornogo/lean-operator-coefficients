import Physics.StandardModel.Spectrum.Representations.SelfDualChirality
import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Physics.FieldTheory.Mass.SelfDualMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.SelfDualChirality instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SelfDualChirality.evaluateGauge => Physics.SelfDualChirality.evaluateGauge,
  GUT.SelfDualChirality.evaluateGauge.eq_1 => Physics.SelfDualChirality.evaluateGauge.eq_1,
  GUT.SelfDualChirality.evaluateGauge_eq_sum => Physics.SelfDualChirality.evaluateGauge_eq_sum,
  GUT.SelfDualChirality.evaluateGauge_injective => Physics.SelfDualChirality.evaluateGauge_injective,
  GUT.SelfDualChirality.evaluated_target_not_zero => Physics.SelfDualChirality.evaluated_target_not_zero,
  GUT.SelfDualChirality.forgetCharges_chiralDifference => Physics.SelfDualChirality.forgetCharges_chiralDifference,
  GUT.SelfDualChirality.forgotten_target_coefficient => Physics.SelfDualChirality.forgotten_target_coefficient,
  GUT.SelfDualChirality.forgotten_target_ne_zero => Physics.SelfDualChirality.forgotten_target_ne_zero,
  GUT.SelfDualChirality.gaugeDualDifference => Physics.SelfDualChirality.gaugeDualDifference,
  GUT.SelfDualChirality.gaugeDualDifference.eq_1 => Physics.SelfDualChirality.gaugeDualDifference.eq_1,
  GUT.SelfDualChirality.gaugeDualDifference_apply => Physics.SelfDualChirality.gaugeDualDifference_apply,
  GUT.SelfDualChirality.not_has_target_of_inverse_conjugacy => Physics.SelfDualChirality.not_has_target_of_inverse_conjugacy,
  GUT.SelfDualChirality.not_has_target_of_source_equiv => Physics.SelfDualChirality.not_has_target_of_source_equiv,
  GUT.SelfDualChirality.not_has_target_of_zero_source => Physics.SelfDualChirality.not_has_target_of_zero_source,
  GUT.SelfDualChirality.unchargedTarget_apply_neg_smWeight => Physics.SelfDualChirality.unchargedTarget_apply_neg_smWeight,
  GUT.SelfDualChirality.unchargedTarget_apply_smWeight => Physics.SelfDualChirality.unchargedTarget_apply_smWeight
]

assert_compatible GUT.SelfDualChirality.evaluateGauge => Physics.SelfDualChirality.evaluateGauge
assert_compatible GUT.SelfDualChirality.evaluateGauge.eq_1 => Physics.SelfDualChirality.evaluateGauge.eq_1
assert_compatible GUT.SelfDualChirality.evaluateGauge_eq_sum => Physics.SelfDualChirality.evaluateGauge_eq_sum
assert_compatible GUT.SelfDualChirality.evaluateGauge_injective => Physics.SelfDualChirality.evaluateGauge_injective
assert_compatible GUT.SelfDualChirality.evaluated_target_not_zero => Physics.SelfDualChirality.evaluated_target_not_zero
assert_compatible GUT.SelfDualChirality.forgetCharges_chiralDifference => Physics.SelfDualChirality.forgetCharges_chiralDifference
assert_compatible GUT.SelfDualChirality.forgotten_target_coefficient => Physics.SelfDualChirality.forgotten_target_coefficient
assert_compatible GUT.SelfDualChirality.forgotten_target_ne_zero => Physics.SelfDualChirality.forgotten_target_ne_zero
assert_compatible GUT.SelfDualChirality.gaugeDualDifference => Physics.SelfDualChirality.gaugeDualDifference
assert_compatible GUT.SelfDualChirality.gaugeDualDifference.eq_1 => Physics.SelfDualChirality.gaugeDualDifference.eq_1
assert_compatible GUT.SelfDualChirality.gaugeDualDifference_apply => Physics.SelfDualChirality.gaugeDualDifference_apply
assert_compatible GUT.SelfDualChirality.not_has_target_of_inverse_conjugacy => Physics.SelfDualChirality.not_has_target_of_inverse_conjugacy
assert_compatible GUT.SelfDualChirality.not_has_target_of_source_equiv => Physics.SelfDualChirality.not_has_target_of_source_equiv
assert_compatible GUT.SelfDualChirality.not_has_target_of_zero_source => Physics.SelfDualChirality.not_has_target_of_zero_source
assert_compatible GUT.SelfDualChirality.unchargedTarget_apply_neg_smWeight => Physics.SelfDualChirality.unchargedTarget_apply_neg_smWeight
assert_compatible GUT.SelfDualChirality.unchargedTarget_apply_smWeight => Physics.SelfDualChirality.unchargedTarget_apply_smWeight
