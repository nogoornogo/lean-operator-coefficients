import Physics.StandardModel.Operators.Selection.AdmittedCyclicSMProhibition
import Math.RepresentationTheory.AdmittedCyclicProhibition
import Physics.StandardModel.Operators.ProhibitionInputSM
import Physics.StandardModel.Operators.InverseLeptonParitySelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.AdmittedCyclicSMProhibition instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AdmittedCyclicSMProhibition.all_forbidden_iff => Physics.AdmittedCyclicSMProhibition.all_forbidden_iff,
  GUT.AdmittedCyclicSMProhibition.forbidden_iff => Physics.AdmittedCyclicSMProhibition.forbidden_iff,
  GUT.AdmittedCyclicSMProhibition.neutral_b1_content => Physics.AdmittedCyclicSMProhibition.neutral_b1_content,
  GUT.AdmittedCyclicSMProhibition.odd_coefficients_zero => Physics.AdmittedCyclicSMProhibition.odd_coefficients_zero,
  GUT.AdmittedCyclicSMProhibition.raw_filter_not_necessary => Physics.AdmittedCyclicSMProhibition.raw_filter_not_necessary,
  GUT.AdmittedCyclicSMProhibition.tripleQ => Physics.AdmittedCyclicSMProhibition.tripleQ,
  GUT.AdmittedCyclicSMProhibition.tripleQ.eq_1 => Physics.AdmittedCyclicSMProhibition.tripleQ.eq_1
]

assert_compatible GUT.AdmittedCyclicSMProhibition.all_forbidden_iff => Physics.AdmittedCyclicSMProhibition.all_forbidden_iff
assert_compatible GUT.AdmittedCyclicSMProhibition.forbidden_iff => Physics.AdmittedCyclicSMProhibition.forbidden_iff
assert_compatible GUT.AdmittedCyclicSMProhibition.neutral_b1_content => Physics.AdmittedCyclicSMProhibition.neutral_b1_content
assert_compatible GUT.AdmittedCyclicSMProhibition.odd_coefficients_zero => Physics.AdmittedCyclicSMProhibition.odd_coefficients_zero
assert_compatible GUT.AdmittedCyclicSMProhibition.raw_filter_not_necessary => Physics.AdmittedCyclicSMProhibition.raw_filter_not_necessary
assert_compatible GUT.AdmittedCyclicSMProhibition.tripleQ => Physics.AdmittedCyclicSMProhibition.tripleQ
assert_compatible GUT.AdmittedCyclicSMProhibition.tripleQ.eq_1 => Physics.AdmittedCyclicSMProhibition.tripleQ.eq_1
