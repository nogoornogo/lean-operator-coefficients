import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticTwoCompleteness
import Math.Algebra.ScalarDegreeTwo
import Physics.FieldTheory.Jets.LorentzFiniteControls
import Physics.FieldTheory.Jets.DerivativeLiteratureScalar
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticTwoCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticTwoCompleteness.Dir => Physics.ScalarQuarticTwoCompleteness.Dir,
  GUT.ScalarQuarticTwoCompleteness.P => Physics.ScalarQuarticTwoCompleteness.P,
  GUT.ScalarQuarticTwoCompleteness.V => Physics.ScalarQuarticTwoCompleteness.V,
  GUT.ScalarQuarticTwoCompleteness.bilinear => Physics.ScalarQuarticTwoCompleteness.bilinear,
  GUT.ScalarQuarticTwoCompleteness.bilinear_apply => Physics.ScalarQuarticTwoCompleteness.bilinear_apply,
  GUT.ScalarQuarticTwoCompleteness.bilinear_invariant => Physics.ScalarQuarticTwoCompleteness.bilinear_invariant,
  GUT.ScalarQuarticTwoCompleteness.coefficient_dimension => Physics.ScalarQuarticTwoCompleteness.coefficient_dimension,
  GUT.ScalarQuarticTwoCompleteness.field_grade => Physics.ScalarQuarticTwoCompleteness.field_grade,
  GUT.ScalarQuarticTwoCompleteness.field_power_grade => Physics.ScalarQuarticTwoCompleteness.field_power_grade,
  GUT.ScalarQuarticTwoCompleteness.first_grade => Physics.ScalarQuarticTwoCompleteness.first_grade,
  GUT.ScalarQuarticTwoCompleteness.first_product_zero => Physics.ScalarQuarticTwoCompleteness.first_product_zero,
  GUT.ScalarQuarticTwoCompleteness.linearFirst => Physics.ScalarQuarticTwoCompleteness.linearFirst,
  GUT.ScalarQuarticTwoCompleteness.linearFirst.eq_1 => Physics.ScalarQuarticTwoCompleteness.linearFirst.eq_1,
  GUT.ScalarQuarticTwoCompleteness.linearFirst_apply => Physics.ScalarQuarticTwoCompleteness.linearFirst_apply,
  GUT.ScalarQuarticTwoCompleteness.linearFirst_covariant => Physics.ScalarQuarticTwoCompleteness.linearFirst_covariant,
  GUT.ScalarQuarticTwoCompleteness.linearFirst_grade => Physics.ScalarQuarticTwoCompleteness.linearFirst_grade,
  GUT.ScalarQuarticTwoCompleteness.linearFirst_single => Physics.ScalarQuarticTwoCompleteness.linearFirst_single,
  GUT.ScalarQuarticTwoCompleteness.monomial_zero => Physics.ScalarQuarticTwoCompleteness.monomial_zero,
  GUT.ScalarQuarticTwoCompleteness.product_grade => Physics.ScalarQuarticTwoCompleteness.product_grade,
  GUT.ScalarQuarticTwoCompleteness.second_product_zero => Physics.ScalarQuarticTwoCompleteness.second_product_zero,
  GUT.ScalarQuarticTwoCompleteness.selected => Physics.ScalarQuarticTwoCompleteness.selected,
  GUT.ScalarQuarticTwoCompleteness.selected_forbidden => Physics.ScalarQuarticTwoCompleteness.selected_forbidden,
  GUT.ScalarQuarticTwoCompleteness.stable => Physics.ScalarQuarticTwoCompleteness.stable,
  GUT.ScalarQuarticTwoCompleteness.trace => Physics.ScalarQuarticTwoCompleteness.trace,
  GUT.ScalarQuarticTwoCompleteness.whole_grade_zero => Physics.ScalarQuarticTwoCompleteness.whole_grade_zero
]

assert_compatible GUT.ScalarQuarticTwoCompleteness.Dir => Physics.ScalarQuarticTwoCompleteness.Dir
assert_compatible GUT.ScalarQuarticTwoCompleteness.P => Physics.ScalarQuarticTwoCompleteness.P
assert_compatible GUT.ScalarQuarticTwoCompleteness.V => Physics.ScalarQuarticTwoCompleteness.V
assert_compatible GUT.ScalarQuarticTwoCompleteness.bilinear => Physics.ScalarQuarticTwoCompleteness.bilinear
assert_compatible GUT.ScalarQuarticTwoCompleteness.bilinear_apply => Physics.ScalarQuarticTwoCompleteness.bilinear_apply
assert_compatible GUT.ScalarQuarticTwoCompleteness.bilinear_invariant => Physics.ScalarQuarticTwoCompleteness.bilinear_invariant
assert_compatible GUT.ScalarQuarticTwoCompleteness.coefficient_dimension => Physics.ScalarQuarticTwoCompleteness.coefficient_dimension
assert_compatible GUT.ScalarQuarticTwoCompleteness.field_grade => Physics.ScalarQuarticTwoCompleteness.field_grade
assert_compatible GUT.ScalarQuarticTwoCompleteness.field_power_grade => Physics.ScalarQuarticTwoCompleteness.field_power_grade
assert_compatible GUT.ScalarQuarticTwoCompleteness.first_grade => Physics.ScalarQuarticTwoCompleteness.first_grade
assert_compatible GUT.ScalarQuarticTwoCompleteness.first_product_zero => Physics.ScalarQuarticTwoCompleteness.first_product_zero
assert_compatible GUT.ScalarQuarticTwoCompleteness.linearFirst => Physics.ScalarQuarticTwoCompleteness.linearFirst
assert_compatible GUT.ScalarQuarticTwoCompleteness.linearFirst.eq_1 => Physics.ScalarQuarticTwoCompleteness.linearFirst.eq_1
assert_compatible GUT.ScalarQuarticTwoCompleteness.linearFirst_apply => Physics.ScalarQuarticTwoCompleteness.linearFirst_apply
assert_compatible GUT.ScalarQuarticTwoCompleteness.linearFirst_covariant => Physics.ScalarQuarticTwoCompleteness.linearFirst_covariant
assert_compatible GUT.ScalarQuarticTwoCompleteness.linearFirst_grade => Physics.ScalarQuarticTwoCompleteness.linearFirst_grade
assert_compatible GUT.ScalarQuarticTwoCompleteness.linearFirst_single => Physics.ScalarQuarticTwoCompleteness.linearFirst_single
assert_compatible GUT.ScalarQuarticTwoCompleteness.monomial_zero => Physics.ScalarQuarticTwoCompleteness.monomial_zero
assert_compatible GUT.ScalarQuarticTwoCompleteness.product_grade => Physics.ScalarQuarticTwoCompleteness.product_grade
assert_compatible GUT.ScalarQuarticTwoCompleteness.second_product_zero => Physics.ScalarQuarticTwoCompleteness.second_product_zero
assert_compatible GUT.ScalarQuarticTwoCompleteness.selected => Physics.ScalarQuarticTwoCompleteness.selected
assert_compatible GUT.ScalarQuarticTwoCompleteness.selected_forbidden => Physics.ScalarQuarticTwoCompleteness.selected_forbidden
assert_compatible GUT.ScalarQuarticTwoCompleteness.stable => Physics.ScalarQuarticTwoCompleteness.stable
assert_compatible GUT.ScalarQuarticTwoCompleteness.trace => Physics.ScalarQuarticTwoCompleteness.trace
assert_compatible GUT.ScalarQuarticTwoCompleteness.whole_grade_zero => Physics.ScalarQuarticTwoCompleteness.whole_grade_zero
