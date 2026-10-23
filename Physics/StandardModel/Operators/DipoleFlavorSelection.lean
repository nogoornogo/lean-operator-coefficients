import Physics.StandardModel.Operators.Dipole.DipoleFlavorSelection
import Physics.StandardModel.Operators.DipoleSMCoefficient
import Math.LinearAlgebra.SelectedCoefficientInputs
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleFlavorSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleFlavorSelection.Coefficients => Physics.DipoleFlavorSelection.Coefficients,
  GUT.DipoleFlavorSelection.allowed_iff => Physics.DipoleFlavorSelection.allowed_iff,
  GUT.DipoleFlavorSelection.allowed_of_bridge => Physics.DipoleFlavorSelection.allowed_of_bridge,
  GUT.DipoleFlavorSelection.coefficient_exists_iff_shares => Physics.DipoleFlavorSelection.coefficient_exists_iff_shares,
  GUT.DipoleFlavorSelection.evaluation => Physics.DipoleFlavorSelection.evaluation,
  GUT.DipoleFlavorSelection.evaluation_zero_of_distinct_weights => Physics.DipoleFlavorSelection.evaluation_zero_of_distinct_weights,
  GUT.DipoleFlavorSelection.forbidden_of_distinct_weights => Physics.DipoleFlavorSelection.forbidden_of_distinct_weights,
  GUT.DipoleFlavorSelection.realized_iff => Physics.DipoleFlavorSelection.realized_iff,
  GUT.DipoleFlavorSelection.realized_of_residual_factor => Physics.DipoleFlavorSelection.realized_of_residual_factor,
  GUT.DipoleFlavorSelection.realized_of_surjective => Physics.DipoleFlavorSelection.realized_of_surjective,
  GUT.DipoleFlavorSelection.residualSelector => Physics.DipoleFlavorSelection.residualSelector,
  GUT.DipoleFlavorSelection.selector => Physics.DipoleFlavorSelection.selector
]

assert_compatible GUT.DipoleFlavorSelection.Coefficients => Physics.DipoleFlavorSelection.Coefficients
assert_compatible GUT.DipoleFlavorSelection.allowed_iff => Physics.DipoleFlavorSelection.allowed_iff
assert_compatible GUT.DipoleFlavorSelection.allowed_of_bridge => Physics.DipoleFlavorSelection.allowed_of_bridge
assert_compatible GUT.DipoleFlavorSelection.coefficient_exists_iff_shares => Physics.DipoleFlavorSelection.coefficient_exists_iff_shares
assert_compatible GUT.DipoleFlavorSelection.evaluation => Physics.DipoleFlavorSelection.evaluation
assert_compatible GUT.DipoleFlavorSelection.evaluation_zero_of_distinct_weights => Physics.DipoleFlavorSelection.evaluation_zero_of_distinct_weights
assert_compatible GUT.DipoleFlavorSelection.forbidden_of_distinct_weights => Physics.DipoleFlavorSelection.forbidden_of_distinct_weights
assert_compatible GUT.DipoleFlavorSelection.realized_iff => Physics.DipoleFlavorSelection.realized_iff
assert_compatible GUT.DipoleFlavorSelection.realized_of_residual_factor => Physics.DipoleFlavorSelection.realized_of_residual_factor
assert_compatible GUT.DipoleFlavorSelection.realized_of_surjective => Physics.DipoleFlavorSelection.realized_of_surjective
assert_compatible GUT.DipoleFlavorSelection.residualSelector => Physics.DipoleFlavorSelection.residualSelector
assert_compatible GUT.DipoleFlavorSelection.selector => Physics.DipoleFlavorSelection.selector
