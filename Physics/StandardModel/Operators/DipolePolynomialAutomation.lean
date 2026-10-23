import Physics.StandardModel.Operators.Dipole.DipolePolynomialAutomation
import Physics.StandardModel.Operators.DipoleModelInterface
import Math.LinearAlgebra.PolynomialBasisCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipolePolynomialAutomation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipolePolynomialAutomation.certificate => Physics.DipolePolynomialAutomation.certificate,
  GUT.DipolePolynomialAutomation.exists_nonzero_iff => Physics.DipolePolynomialAutomation.exists_nonzero_iff,
  GUT.DipolePolynomialAutomation.register => Physics.DipolePolynomialAutomation.register,
  GUT.DipolePolynomialAutomation.residual_expansion => Physics.DipolePolynomialAutomation.residual_expansion,
  GUT.DipolePolynomialAutomation.selected => Physics.DipolePolynomialAutomation.selected
]

assert_compatible GUT.DipolePolynomialAutomation.certificate => Physics.DipolePolynomialAutomation.certificate
assert_compatible GUT.DipolePolynomialAutomation.exists_nonzero_iff => Physics.DipolePolynomialAutomation.exists_nonzero_iff
assert_compatible GUT.DipolePolynomialAutomation.register => Physics.DipolePolynomialAutomation.register
assert_compatible GUT.DipolePolynomialAutomation.residual_expansion => Physics.DipolePolynomialAutomation.residual_expansion
assert_compatible GUT.DipolePolynomialAutomation.selected => Physics.DipolePolynomialAutomation.selected
