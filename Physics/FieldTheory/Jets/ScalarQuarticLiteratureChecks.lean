import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticLiteratureChecks
import Physics.FieldTheory.Jets.ScalarQuarticFourChecks
import Physics.FieldTheory.Jets.ScalarZeroDerivativeCertificate
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticLiteratureChecks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticLiteratureChecks.admitted_triple => Physics.ScalarQuarticLiteratureChecks.admitted_triple,
  GUT.ScalarQuarticLiteratureChecks.bounded_counts => Physics.ScalarQuarticLiteratureChecks.bounded_counts,
  GUT.ScalarQuarticLiteratureChecks.chosen => Physics.ScalarQuarticLiteratureChecks.chosen,
  GUT.ScalarQuarticLiteratureChecks.chosen.eq_1 => Physics.ScalarQuarticLiteratureChecks.chosen.eq_1,
  GUT.ScalarQuarticLiteratureChecks.chosenEquivalence => Physics.ScalarQuarticLiteratureChecks.chosenEquivalence,
  GUT.ScalarQuarticLiteratureChecks.chosen_density => Physics.ScalarQuarticLiteratureChecks.chosen_density,
  GUT.ScalarQuarticLiteratureChecks.chosen_extraction => Physics.ScalarQuarticLiteratureChecks.chosen_extraction,
  GUT.ScalarQuarticLiteratureChecks.chosen_inverse => Physics.ScalarQuarticLiteratureChecks.chosen_inverse,
  GUT.ScalarQuarticLiteratureChecks.chosen_reconstruction => Physics.ScalarQuarticLiteratureChecks.chosen_reconstruction,
  GUT.ScalarQuarticLiteratureChecks.chosen_value => Physics.ScalarQuarticLiteratureChecks.chosen_value,
  GUT.ScalarQuarticLiteratureChecks.first => Physics.ScalarQuarticLiteratureChecks.first,
  GUT.ScalarQuarticLiteratureChecks.first_value => Physics.ScalarQuarticLiteratureChecks.first_value,
  GUT.ScalarQuarticLiteratureChecks.independent_values_rejected => Physics.ScalarQuarticLiteratureChecks.independent_values_rejected,
  GUT.ScalarQuarticLiteratureChecks.normalized_first => Physics.ScalarQuarticLiteratureChecks.normalized_first,
  GUT.ScalarQuarticLiteratureChecks.normalized_second => Physics.ScalarQuarticLiteratureChecks.normalized_second,
  GUT.ScalarQuarticLiteratureChecks.normalized_third => Physics.ScalarQuarticLiteratureChecks.normalized_third,
  GUT.ScalarQuarticLiteratureChecks.second => Physics.ScalarQuarticLiteratureChecks.second,
  GUT.ScalarQuarticLiteratureChecks.second_value => Physics.ScalarQuarticLiteratureChecks.second_value,
  GUT.ScalarQuarticLiteratureChecks.third => Physics.ScalarQuarticLiteratureChecks.third,
  GUT.ScalarQuarticLiteratureChecks.third_value => Physics.ScalarQuarticLiteratureChecks.third_value,
  GUT.ScalarQuarticLiteratureChecks.value => Physics.ScalarQuarticLiteratureChecks.value
]

assert_compatible GUT.ScalarQuarticLiteratureChecks.admitted_triple => Physics.ScalarQuarticLiteratureChecks.admitted_triple
assert_compatible GUT.ScalarQuarticLiteratureChecks.bounded_counts => Physics.ScalarQuarticLiteratureChecks.bounded_counts
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen => Physics.ScalarQuarticLiteratureChecks.chosen
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen.eq_1 => Physics.ScalarQuarticLiteratureChecks.chosen.eq_1
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosenEquivalence => Physics.ScalarQuarticLiteratureChecks.chosenEquivalence
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen_density => Physics.ScalarQuarticLiteratureChecks.chosen_density
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen_extraction => Physics.ScalarQuarticLiteratureChecks.chosen_extraction
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen_inverse => Physics.ScalarQuarticLiteratureChecks.chosen_inverse
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen_reconstruction => Physics.ScalarQuarticLiteratureChecks.chosen_reconstruction
assert_compatible GUT.ScalarQuarticLiteratureChecks.chosen_value => Physics.ScalarQuarticLiteratureChecks.chosen_value
assert_compatible GUT.ScalarQuarticLiteratureChecks.first => Physics.ScalarQuarticLiteratureChecks.first
assert_compatible GUT.ScalarQuarticLiteratureChecks.first_value => Physics.ScalarQuarticLiteratureChecks.first_value
assert_compatible GUT.ScalarQuarticLiteratureChecks.independent_values_rejected => Physics.ScalarQuarticLiteratureChecks.independent_values_rejected
assert_compatible GUT.ScalarQuarticLiteratureChecks.normalized_first => Physics.ScalarQuarticLiteratureChecks.normalized_first
assert_compatible GUT.ScalarQuarticLiteratureChecks.normalized_second => Physics.ScalarQuarticLiteratureChecks.normalized_second
assert_compatible GUT.ScalarQuarticLiteratureChecks.normalized_third => Physics.ScalarQuarticLiteratureChecks.normalized_third
assert_compatible GUT.ScalarQuarticLiteratureChecks.second => Physics.ScalarQuarticLiteratureChecks.second
assert_compatible GUT.ScalarQuarticLiteratureChecks.second_value => Physics.ScalarQuarticLiteratureChecks.second_value
assert_compatible GUT.ScalarQuarticLiteratureChecks.third => Physics.ScalarQuarticLiteratureChecks.third
assert_compatible GUT.ScalarQuarticLiteratureChecks.third_value => Physics.ScalarQuarticLiteratureChecks.third_value
assert_compatible GUT.ScalarQuarticLiteratureChecks.value => Physics.ScalarQuarticLiteratureChecks.value
