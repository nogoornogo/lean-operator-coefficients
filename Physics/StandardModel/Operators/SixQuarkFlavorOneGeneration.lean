import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorOneGeneration
import Physics.StandardModel.Operators.SixQuarkFlavorResidualHom
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorOneGeneration instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SixQuarkFlavorOneGeneration.addFlavor => Physics.SixQuarkFlavorOneGeneration.addFlavor,
  GUT.SixQuarkFlavorOneGeneration.finrank_scalarFlavor => Physics.SixQuarkFlavorOneGeneration.finrank_scalarFlavor,
  GUT.SixQuarkFlavorOneGeneration.finrank_scalarHom => Physics.SixQuarkFlavorOneGeneration.finrank_scalarHom,
  GUT.SixQuarkFlavorOneGeneration.forgetFlavor => Physics.SixQuarkFlavorOneGeneration.forgetFlavor,
  GUT.SixQuarkFlavorOneGeneration.homTwoProbeEquiv => Physics.SixQuarkFlavorOneGeneration.homTwoProbeEquiv,
  GUT.SixQuarkFlavorOneGeneration.scalarAction => Physics.SixQuarkFlavorOneGeneration.scalarAction,
  GUT.SixQuarkFlavorOneGeneration.scalarFlavorEquiv => Physics.SixQuarkFlavorOneGeneration.scalarFlavorEquiv,
  GUT.SixQuarkFlavorOneGeneration.twoProbeEquiv => Physics.SixQuarkFlavorOneGeneration.twoProbeEquiv
]

assert_compatible GUT.SixQuarkFlavorOneGeneration.addFlavor => Physics.SixQuarkFlavorOneGeneration.addFlavor
assert_compatible GUT.SixQuarkFlavorOneGeneration.finrank_scalarFlavor => Physics.SixQuarkFlavorOneGeneration.finrank_scalarFlavor
assert_compatible GUT.SixQuarkFlavorOneGeneration.finrank_scalarHom => Physics.SixQuarkFlavorOneGeneration.finrank_scalarHom
assert_compatible GUT.SixQuarkFlavorOneGeneration.forgetFlavor => Physics.SixQuarkFlavorOneGeneration.forgetFlavor
assert_compatible GUT.SixQuarkFlavorOneGeneration.homTwoProbeEquiv => Physics.SixQuarkFlavorOneGeneration.homTwoProbeEquiv
assert_compatible GUT.SixQuarkFlavorOneGeneration.scalarAction => Physics.SixQuarkFlavorOneGeneration.scalarAction
assert_compatible GUT.SixQuarkFlavorOneGeneration.scalarFlavorEquiv => Physics.SixQuarkFlavorOneGeneration.scalarFlavorEquiv
assert_compatible GUT.SixQuarkFlavorOneGeneration.twoProbeEquiv => Physics.SixQuarkFlavorOneGeneration.twoProbeEquiv
