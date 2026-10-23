import Physics.StandardModel.Operators.Dipole.ComposableDipoleSelection
import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.LinearAlgebra.CoefficientSelectorComposition
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.ComposableDipoleSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ComposableDipoleSelection.extraction => Physics.ComposableDipoleSelection.extraction,
  GUT.ComposableDipoleSelection.forbidden_iff => Physics.ComposableDipoleSelection.forbidden_iff,
  GUT.ComposableDipoleSelection.forbidden_of_weights => Physics.ComposableDipoleSelection.forbidden_of_weights,
  GUT.ComposableDipoleSelection.residual => Physics.ComposableDipoleSelection.residual,
  GUT.ComposableDipoleSelection.selector => Physics.ComposableDipoleSelection.selector
]

assert_compatible GUT.ComposableDipoleSelection.extraction => Physics.ComposableDipoleSelection.extraction
assert_compatible GUT.ComposableDipoleSelection.forbidden_iff => Physics.ComposableDipoleSelection.forbidden_iff
assert_compatible GUT.ComposableDipoleSelection.forbidden_of_weights => Physics.ComposableDipoleSelection.forbidden_of_weights
assert_compatible GUT.ComposableDipoleSelection.residual => Physics.ComposableDipoleSelection.residual
assert_compatible GUT.ComposableDipoleSelection.selector => Physics.ComposableDipoleSelection.selector
