import Physics.StandardModel.Operators.Selection.ScalarResidualSelection
import Physics.StandardModel.Operators.ResidualSelectionCriteria
import Physics.StandardModel.Operators.QqqlScalarFlavor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.ScalarResidualSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarResidualSelection.Four => Physics.ScalarResidualSelection.Four,
  GUT.ScalarResidualSelection.Neutral => Physics.ScalarResidualSelection.Neutral,
  GUT.ScalarResidualSelection.allowed_four => Physics.ScalarResidualSelection.allowed_four,
  GUT.ScalarResidualSelection.allowed_qqql => Physics.ScalarResidualSelection.allowed_qqql,
  GUT.ScalarResidualSelection.allowed_qque => Physics.ScalarResidualSelection.allowed_qque,
  GUT.ScalarResidualSelection.allowed_total => Physics.ScalarResidualSelection.allowed_total,
  GUT.ScalarResidualSelection.coefficient => Physics.ScalarResidualSelection.coefficient,
  GUT.ScalarResidualSelection.coefficient.eq_1 => Physics.ScalarResidualSelection.coefficient.eq_1,
  GUT.ScalarResidualSelection.scalar_formula => Physics.ScalarResidualSelection.scalar_formula
]

assert_compatible GUT.ScalarResidualSelection.Four => Physics.ScalarResidualSelection.Four
assert_compatible GUT.ScalarResidualSelection.Neutral => Physics.ScalarResidualSelection.Neutral
assert_compatible GUT.ScalarResidualSelection.allowed_four => Physics.ScalarResidualSelection.allowed_four
assert_compatible GUT.ScalarResidualSelection.allowed_qqql => Physics.ScalarResidualSelection.allowed_qqql
assert_compatible GUT.ScalarResidualSelection.allowed_qque => Physics.ScalarResidualSelection.allowed_qque
assert_compatible GUT.ScalarResidualSelection.allowed_total => Physics.ScalarResidualSelection.allowed_total
assert_compatible GUT.ScalarResidualSelection.coefficient => Physics.ScalarResidualSelection.coefficient
assert_compatible GUT.ScalarResidualSelection.coefficient.eq_1 => Physics.ScalarResidualSelection.coefficient.eq_1
assert_compatible GUT.ScalarResidualSelection.scalar_formula => Physics.ScalarResidualSelection.scalar_formula
