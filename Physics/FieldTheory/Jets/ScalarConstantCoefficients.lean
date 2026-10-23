import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarConstantCoefficients
import Math.RepresentationTheory.JetConstantProjection
import Physics.FieldTheory.Jets.ScalarProhibitionConditions
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarConstantCoefficients instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarConstantCoefficients.coefficient => Physics.ScalarConstantCoefficients.coefficient,
  GUT.ScalarConstantCoefficients.coefficient_relations => Physics.ScalarConstantCoefficients.coefficient_relations,
  GUT.ScalarConstantCoefficients.cubic_value_iff => Physics.ScalarConstantCoefficients.cubic_value_iff,
  GUT.ScalarConstantCoefficients.detects => Physics.ScalarConstantCoefficients.detects,
  GUT.ScalarConstantCoefficients.evaluation => Physics.ScalarConstantCoefficients.evaluation,
  GUT.ScalarConstantCoefficients.evaluation_ideal => Physics.ScalarConstantCoefficients.evaluation_ideal,
  GUT.ScalarConstantCoefficients.evaluation_invariant => Physics.ScalarConstantCoefficients.evaluation_invariant,
  GUT.ScalarConstantCoefficients.functional => Physics.ScalarConstantCoefficients.functional,
  GUT.ScalarConstantCoefficients.nonzero => Physics.ScalarConstantCoefficients.nonzero,
  GUT.ScalarConstantCoefficients.nonzero_cubic_iff => Physics.ScalarConstantCoefficients.nonzero_cubic_iff
]

assert_compatible GUT.ScalarConstantCoefficients.coefficient => Physics.ScalarConstantCoefficients.coefficient
assert_compatible GUT.ScalarConstantCoefficients.coefficient_relations => Physics.ScalarConstantCoefficients.coefficient_relations
assert_compatible GUT.ScalarConstantCoefficients.cubic_value_iff => Physics.ScalarConstantCoefficients.cubic_value_iff
assert_compatible GUT.ScalarConstantCoefficients.detects => Physics.ScalarConstantCoefficients.detects
assert_compatible GUT.ScalarConstantCoefficients.evaluation => Physics.ScalarConstantCoefficients.evaluation
assert_compatible GUT.ScalarConstantCoefficients.evaluation_ideal => Physics.ScalarConstantCoefficients.evaluation_ideal
assert_compatible GUT.ScalarConstantCoefficients.evaluation_invariant => Physics.ScalarConstantCoefficients.evaluation_invariant
assert_compatible GUT.ScalarConstantCoefficients.functional => Physics.ScalarConstantCoefficients.functional
assert_compatible GUT.ScalarConstantCoefficients.nonzero => Physics.ScalarConstantCoefficients.nonzero
assert_compatible GUT.ScalarConstantCoefficients.nonzero_cubic_iff => Physics.ScalarConstantCoefficients.nonzero_cubic_iff
