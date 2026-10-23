import Physics.StandardModel.Spectrum.Representations.ConjugationPartialTarget
import Physics.StandardModel.Spectrum.ConjugationDualIndex
import Physics.StandardModel.Spectrum.SMPartialTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ConjugationPartialTarget instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ConjugationDualIndex.dualIndex.congr_simp => Physics.ConjugationDualIndex.dualIndex.congr_simp,
  GUT.ConjugationPartialTarget.HasPartialTarget => Physics.ConjugationPartialTarget.HasPartialTarget,
  GUT.ConjugationPartialTarget.chargesSupported => Physics.ConjugationPartialTarget.chargesSupported,
  GUT.ConjugationPartialTarget.exists_actual_signature_pair => Physics.ConjugationPartialTarget.exists_actual_signature_pair,
  GUT.ConjugationPartialTarget.exists_zeroMode => Physics.ConjugationPartialTarget.exists_zeroMode,
  GUT.ConjugationPartialTarget.of_full_target => Physics.ConjugationPartialTarget.of_full_target,
  GUT.ConjugationPartialTarget.profiles_compatible => Physics.ConjugationPartialTarget.profiles_compatible,
  GUT.ConjugationPartialTarget.selection_rule_obstruction => Physics.ConjugationPartialTarget.selection_rule_obstruction
]

assert_compatible GUT.ConjugationDualIndex.dualIndex.congr_simp => Physics.ConjugationDualIndex.dualIndex.congr_simp
assert_compatible GUT.ConjugationPartialTarget.HasPartialTarget => Physics.ConjugationPartialTarget.HasPartialTarget
assert_compatible GUT.ConjugationPartialTarget.chargesSupported => Physics.ConjugationPartialTarget.chargesSupported
assert_compatible GUT.ConjugationPartialTarget.exists_actual_signature_pair => Physics.ConjugationPartialTarget.exists_actual_signature_pair
assert_compatible GUT.ConjugationPartialTarget.exists_zeroMode => Physics.ConjugationPartialTarget.exists_zeroMode
assert_compatible GUT.ConjugationPartialTarget.of_full_target => Physics.ConjugationPartialTarget.of_full_target
assert_compatible GUT.ConjugationPartialTarget.profiles_compatible => Physics.ConjugationPartialTarget.profiles_compatible
assert_compatible GUT.ConjugationPartialTarget.selection_rule_obstruction => Physics.ConjugationPartialTarget.selection_rule_obstruction
