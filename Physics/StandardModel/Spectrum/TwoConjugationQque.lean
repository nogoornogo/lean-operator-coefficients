import Physics.StandardModel.Spectrum.Representations.TwoConjugationQque
import Physics.StandardModel.Spectrum.ConjugationPartialTarget
import Physics.StandardModel.Operators.SlotSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.TwoConjugationQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.TwoConjugationQque.exists_actual_signature_pair => Physics.TwoConjugationQque.exists_actual_signature_pair,
  GUT.TwoConjugationQque.exists_common_charge => Physics.TwoConjugationQque.exists_common_charge,
  GUT.TwoConjugationQque.exists_supported_qque => Physics.TwoConjugationQque.exists_supported_qque,
  GUT.TwoConjugationQque.legacy_selection_rule_obstruction => Physics.TwoConjugationQque.legacy_selection_rule_obstruction,
  GUT.TwoConjugationQque.profiles_compatible => Physics.TwoConjugationQque.profiles_compatible,
  GUT.TwoConjugationQque.qqueCharges => Physics.TwoConjugationQque.qqueCharges,
  GUT.TwoConjugationQque.qqueCharges.eq_1 => Physics.TwoConjugationQque.qqueCharges.eq_1,
  GUT.TwoConjugationQque.qqueCharges_neutral => Physics.TwoConjugationQque.qqueCharges_neutral,
  GUT.TwoConjugationQque.quark_profiles_compatible => Physics.TwoConjugationQque.quark_profiles_compatible,
  GUT.TwoConjugationQque.selection_rule_obstruction => Physics.TwoConjugationQque.selection_rule_obstruction,
  GUT.TwoConjugationQque.slotwise_selection_rule_obstruction => Physics.TwoConjugationQque.slotwise_selection_rule_obstruction
]

assert_compatible GUT.TwoConjugationQque.exists_actual_signature_pair => Physics.TwoConjugationQque.exists_actual_signature_pair
assert_compatible GUT.TwoConjugationQque.exists_common_charge => Physics.TwoConjugationQque.exists_common_charge
assert_compatible GUT.TwoConjugationQque.exists_supported_qque => Physics.TwoConjugationQque.exists_supported_qque
assert_compatible GUT.TwoConjugationQque.legacy_selection_rule_obstruction => Physics.TwoConjugationQque.legacy_selection_rule_obstruction
assert_compatible GUT.TwoConjugationQque.profiles_compatible => Physics.TwoConjugationQque.profiles_compatible
assert_compatible GUT.TwoConjugationQque.qqueCharges => Physics.TwoConjugationQque.qqueCharges
assert_compatible GUT.TwoConjugationQque.qqueCharges.eq_1 => Physics.TwoConjugationQque.qqueCharges.eq_1
assert_compatible GUT.TwoConjugationQque.qqueCharges_neutral => Physics.TwoConjugationQque.qqueCharges_neutral
assert_compatible GUT.TwoConjugationQque.quark_profiles_compatible => Physics.TwoConjugationQque.quark_profiles_compatible
assert_compatible GUT.TwoConjugationQque.selection_rule_obstruction => Physics.TwoConjugationQque.selection_rule_obstruction
assert_compatible GUT.TwoConjugationQque.slotwise_selection_rule_obstruction => Physics.TwoConjugationQque.slotwise_selection_rule_obstruction
