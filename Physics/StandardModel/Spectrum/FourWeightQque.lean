import Physics.StandardModel.Spectrum.Representations.FourWeightQque
import Physics.StandardModel.Spectrum.TwoConjugationQque
import Physics.StandardModel.Spectrum.QqueLocalTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.FourWeightQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourWeightQque.HasTarget => Physics.FourWeightQque.HasTarget,
  GUT.FourWeightQque.exists_supported_qque => Physics.FourWeightQque.exists_supported_qque,
  GUT.FourWeightQque.exists_zeroMode => Physics.FourWeightQque.exists_zeroMode,
  GUT.FourWeightQque.of_partial_target => Physics.FourWeightQque.of_partial_target,
  GUT.FourWeightQque.quark_profiles_compatible => Physics.FourWeightQque.quark_profiles_compatible,
  GUT.FourWeightQque.slotwise_selection_rule_obstruction => Physics.FourWeightQque.slotwise_selection_rule_obstruction
]

assert_compatible GUT.FourWeightQque.HasTarget => Physics.FourWeightQque.HasTarget
assert_compatible GUT.FourWeightQque.exists_supported_qque => Physics.FourWeightQque.exists_supported_qque
assert_compatible GUT.FourWeightQque.exists_zeroMode => Physics.FourWeightQque.exists_zeroMode
assert_compatible GUT.FourWeightQque.of_partial_target => Physics.FourWeightQque.of_partial_target
assert_compatible GUT.FourWeightQque.quark_profiles_compatible => Physics.FourWeightQque.quark_profiles_compatible
assert_compatible GUT.FourWeightQque.slotwise_selection_rule_obstruction => Physics.FourWeightQque.slotwise_selection_rule_obstruction
