import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarCompletenessChecks
import Physics.FieldTheory.Jets.ScalarQuarticContractions
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarCompletenessChecks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarCompletenessChecks.Cao.coefficient_value => Physics.ScalarCompletenessChecks.Cao.coefficient_value,
  GUT.ScalarCompletenessChecks.Cao.combination => Physics.ScalarCompletenessChecks.Cao.combination,
  GUT.ScalarCompletenessChecks.Cao.combination.eq_1 => Physics.ScalarCompletenessChecks.Cao.combination.eq_1,
  GUT.ScalarCompletenessChecks.Cao.nonzero => Physics.ScalarCompletenessChecks.Cao.nonzero,
  GUT.ScalarCompletenessChecks.Cao.o1 => Physics.ScalarCompletenessChecks.Cao.o1,
  GUT.ScalarCompletenessChecks.Cao.o1.eq_1 => Physics.ScalarCompletenessChecks.Cao.o1.eq_1,
  GUT.ScalarCompletenessChecks.Cao.o2 => Physics.ScalarCompletenessChecks.Cao.o2,
  GUT.ScalarCompletenessChecks.Cao.o2.eq_1 => Physics.ScalarCompletenessChecks.Cao.o2.eq_1,
  GUT.ScalarCompletenessChecks.Cao.o3 => Physics.ScalarCompletenessChecks.Cao.o3,
  GUT.ScalarCompletenessChecks.Cao.o3.eq_1 => Physics.ScalarCompletenessChecks.Cao.o3.eq_1,
  GUT.ScalarCompletenessChecks.Cao.quotient_normalization => Physics.ScalarCompletenessChecks.Cao.quotient_normalization,
  GUT.ScalarCompletenessChecks.Cao.separator_value => Physics.ScalarCompletenessChecks.Cao.separator_value,
  GUT.ScalarCompletenessChecks.Four.coefficient_A => Physics.ScalarCompletenessChecks.Four.coefficient_A,
  GUT.ScalarCompletenessChecks.Four.coefficient_B => Physics.ScalarCompletenessChecks.Four.coefficient_B,
  GUT.ScalarCompletenessChecks.Four.helper_coefficients => Physics.ScalarCompletenessChecks.Four.helper_coefficients,
  GUT.ScalarCompletenessChecks.Four.helper_nonzero => Physics.ScalarCompletenessChecks.Four.helper_nonzero,
  GUT.ScalarCompletenessChecks.Two.anisotropic => Physics.ScalarCompletenessChecks.Two.anisotropic,
  GUT.ScalarCompletenessChecks.Two.anisotropic.eq_1 => Physics.ScalarCompletenessChecks.Two.anisotropic.eq_1,
  GUT.ScalarCompletenessChecks.Two.anisotropic_coefficient_rejected => Physics.ScalarCompletenessChecks.Two.anisotropic_coefficient_rejected,
  GUT.ScalarCompletenessChecks.Two.anisotropic_grade => Physics.ScalarCompletenessChecks.Two.anisotropic_grade,
  GUT.ScalarCompletenessChecks.Two.anisotropic_nonzero => Physics.ScalarCompletenessChecks.Two.anisotropic_nonzero,
  GUT.ScalarCompletenessChecks.Two.anisotropic_value => Physics.ScalarCompletenessChecks.Two.anisotropic_value,
  GUT.ScalarCompletenessChecks.Two.global_zero => Physics.ScalarCompletenessChecks.Two.global_zero,
  GUT.ScalarCompletenessChecks.Two.helper_zero => Physics.ScalarCompletenessChecks.Two.helper_zero
]

assert_compatible GUT.ScalarCompletenessChecks.Cao.coefficient_value => Physics.ScalarCompletenessChecks.Cao.coefficient_value
assert_compatible GUT.ScalarCompletenessChecks.Cao.combination => Physics.ScalarCompletenessChecks.Cao.combination
assert_compatible GUT.ScalarCompletenessChecks.Cao.combination.eq_1 => Physics.ScalarCompletenessChecks.Cao.combination.eq_1
assert_compatible GUT.ScalarCompletenessChecks.Cao.nonzero => Physics.ScalarCompletenessChecks.Cao.nonzero
assert_compatible GUT.ScalarCompletenessChecks.Cao.o1 => Physics.ScalarCompletenessChecks.Cao.o1
assert_compatible GUT.ScalarCompletenessChecks.Cao.o1.eq_1 => Physics.ScalarCompletenessChecks.Cao.o1.eq_1
assert_compatible GUT.ScalarCompletenessChecks.Cao.o2 => Physics.ScalarCompletenessChecks.Cao.o2
assert_compatible GUT.ScalarCompletenessChecks.Cao.o2.eq_1 => Physics.ScalarCompletenessChecks.Cao.o2.eq_1
assert_compatible GUT.ScalarCompletenessChecks.Cao.o3 => Physics.ScalarCompletenessChecks.Cao.o3
assert_compatible GUT.ScalarCompletenessChecks.Cao.o3.eq_1 => Physics.ScalarCompletenessChecks.Cao.o3.eq_1
assert_compatible GUT.ScalarCompletenessChecks.Cao.quotient_normalization => Physics.ScalarCompletenessChecks.Cao.quotient_normalization
assert_compatible GUT.ScalarCompletenessChecks.Cao.separator_value => Physics.ScalarCompletenessChecks.Cao.separator_value
assert_compatible GUT.ScalarCompletenessChecks.Four.coefficient_A => Physics.ScalarCompletenessChecks.Four.coefficient_A
assert_compatible GUT.ScalarCompletenessChecks.Four.coefficient_B => Physics.ScalarCompletenessChecks.Four.coefficient_B
assert_compatible GUT.ScalarCompletenessChecks.Four.helper_coefficients => Physics.ScalarCompletenessChecks.Four.helper_coefficients
assert_compatible GUT.ScalarCompletenessChecks.Four.helper_nonzero => Physics.ScalarCompletenessChecks.Four.helper_nonzero
assert_compatible GUT.ScalarCompletenessChecks.Two.anisotropic => Physics.ScalarCompletenessChecks.Two.anisotropic
assert_compatible GUT.ScalarCompletenessChecks.Two.anisotropic.eq_1 => Physics.ScalarCompletenessChecks.Two.anisotropic.eq_1
assert_compatible GUT.ScalarCompletenessChecks.Two.anisotropic_coefficient_rejected => Physics.ScalarCompletenessChecks.Two.anisotropic_coefficient_rejected
assert_compatible GUT.ScalarCompletenessChecks.Two.anisotropic_grade => Physics.ScalarCompletenessChecks.Two.anisotropic_grade
assert_compatible GUT.ScalarCompletenessChecks.Two.anisotropic_nonzero => Physics.ScalarCompletenessChecks.Two.anisotropic_nonzero
assert_compatible GUT.ScalarCompletenessChecks.Two.anisotropic_value => Physics.ScalarCompletenessChecks.Two.anisotropic_value
assert_compatible GUT.ScalarCompletenessChecks.Two.global_zero => Physics.ScalarCompletenessChecks.Two.global_zero
assert_compatible GUT.ScalarCompletenessChecks.Two.helper_zero => Physics.ScalarCompletenessChecks.Two.helper_zero
