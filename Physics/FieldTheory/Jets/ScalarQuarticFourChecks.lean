import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourChecks
import Physics.FieldTheory.Jets.ScalarQuarticFourCompleteness
import Physics.FieldTheory.Jets.ScalarCompletenessChecks
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourChecks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticFourChecks.A_value => Physics.ScalarQuarticFourChecks.A_value,
  GUT.ScalarQuarticFourChecks.B_value => Physics.ScalarQuarticFourChecks.B_value,
  GUT.ScalarQuarticFourChecks.Cao_value => Physics.ScalarQuarticFourChecks.Cao_value,
  GUT.ScalarQuarticFourChecks.coefficient_scope_control => Physics.ScalarQuarticFourChecks.coefficient_scope_control,
  GUT.ScalarQuarticFourChecks.normalized_extraction => Physics.ScalarQuarticFourChecks.normalized_extraction,
  GUT.ScalarQuarticFourChecks.probe => Physics.ScalarQuarticFourChecks.probe,
  GUT.ScalarQuarticFourChecks.probe.eq_1 => Physics.ScalarQuarticFourChecks.probe.eq_1,
  GUT.ScalarQuarticFourChecks.probe_grade => Physics.ScalarQuarticFourChecks.probe_grade,
  GUT.ScalarQuarticFourChecks.probe_not_in_candidate_image => Physics.ScalarQuarticFourChecks.probe_not_in_candidate_image,
  GUT.ScalarQuarticFourChecks.probe_transformed_value => Physics.ScalarQuarticFourChecks.probe_transformed_value,
  GUT.ScalarQuarticFourChecks.probe_value => Physics.ScalarQuarticFourChecks.probe_value,
  GUT.ScalarQuarticFourChecks.probe_word => Physics.ScalarQuarticFourChecks.probe_word,
  GUT.ScalarQuarticFourChecks.quotientFunctional => Physics.ScalarQuarticFourChecks.quotientFunctional,
  GUT.ScalarQuarticFourChecks.quotient_evaluation => Physics.ScalarQuarticFourChecks.quotient_evaluation,
  GUT.ScalarQuarticFourChecks.quotient_extraction => Physics.ScalarQuarticFourChecks.quotient_extraction,
  GUT.ScalarQuarticFourChecks.restriction_coordinate => Physics.ScalarQuarticFourChecks.restriction_coordinate,
  GUT.ScalarQuarticFourChecks.restriction_reconstruction => Physics.ScalarQuarticFourChecks.restriction_reconstruction
]

assert_compatible GUT.ScalarQuarticFourChecks.A_value => Physics.ScalarQuarticFourChecks.A_value
assert_compatible GUT.ScalarQuarticFourChecks.B_value => Physics.ScalarQuarticFourChecks.B_value
assert_compatible GUT.ScalarQuarticFourChecks.Cao_value => Physics.ScalarQuarticFourChecks.Cao_value
assert_compatible GUT.ScalarQuarticFourChecks.coefficient_scope_control => Physics.ScalarQuarticFourChecks.coefficient_scope_control
assert_compatible GUT.ScalarQuarticFourChecks.normalized_extraction => Physics.ScalarQuarticFourChecks.normalized_extraction
assert_compatible GUT.ScalarQuarticFourChecks.probe => Physics.ScalarQuarticFourChecks.probe
assert_compatible GUT.ScalarQuarticFourChecks.probe.eq_1 => Physics.ScalarQuarticFourChecks.probe.eq_1
assert_compatible GUT.ScalarQuarticFourChecks.probe_grade => Physics.ScalarQuarticFourChecks.probe_grade
assert_compatible GUT.ScalarQuarticFourChecks.probe_not_in_candidate_image => Physics.ScalarQuarticFourChecks.probe_not_in_candidate_image
assert_compatible GUT.ScalarQuarticFourChecks.probe_transformed_value => Physics.ScalarQuarticFourChecks.probe_transformed_value
assert_compatible GUT.ScalarQuarticFourChecks.probe_value => Physics.ScalarQuarticFourChecks.probe_value
assert_compatible GUT.ScalarQuarticFourChecks.probe_word => Physics.ScalarQuarticFourChecks.probe_word
assert_compatible GUT.ScalarQuarticFourChecks.quotientFunctional => Physics.ScalarQuarticFourChecks.quotientFunctional
assert_compatible GUT.ScalarQuarticFourChecks.quotient_evaluation => Physics.ScalarQuarticFourChecks.quotient_evaluation
assert_compatible GUT.ScalarQuarticFourChecks.quotient_extraction => Physics.ScalarQuarticFourChecks.quotient_extraction
assert_compatible GUT.ScalarQuarticFourChecks.restriction_coordinate => Physics.ScalarQuarticFourChecks.restriction_coordinate
assert_compatible GUT.ScalarQuarticFourChecks.restriction_reconstruction => Physics.ScalarQuarticFourChecks.restriction_reconstruction
