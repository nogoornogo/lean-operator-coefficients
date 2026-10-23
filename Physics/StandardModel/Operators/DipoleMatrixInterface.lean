import Physics.StandardModel.Operators.Dipole.DipoleMatrixInterface
import Physics.StandardModel.Operators.DipoleModelInterface
import Math.RepresentationTheory.MatrixIntertwiner
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleMatrixInterface instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleMatrixInterface.register => Physics.DipoleMatrixInterface.register,
  GUT.DipoleMatrixInterface.register.eq_1 => Physics.DipoleMatrixInterface.register.eq_1,
  GUT.DipoleMatrixInterface.selected_entry => Physics.DipoleMatrixInterface.selected_entry
]

assert_compatible GUT.DipoleMatrixInterface.register => Physics.DipoleMatrixInterface.register
assert_compatible GUT.DipoleMatrixInterface.register.eq_1 => Physics.DipoleMatrixInterface.register.eq_1
assert_compatible GUT.DipoleMatrixInterface.selected_entry => Physics.DipoleMatrixInterface.selected_entry
