import Physics.StandardModel.Operators.Dipole.CyclicBasisDipoleSelection
import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.RepresentationTheory.CyclicWeightCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.CyclicBasisDipoleSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CyclicBasisDipoleSelection.matrixUnit => Physics.CyclicBasisDipoleSelection.matrixUnit,
  GUT.CyclicBasisDipoleSelection.matrixUnit.eq_1 => Physics.CyclicBasisDipoleSelection.matrixUnit.eq_1,
  GUT.CyclicBasisDipoleSelection.matrixUnit_selected => Physics.CyclicBasisDipoleSelection.matrixUnit_selected,
  GUT.CyclicBasisDipoleSelection.selected_allowed_iff => Physics.CyclicBasisDipoleSelection.selected_allowed_iff,
  GUT.CyclicBasisDipoleSelection.selected_forbidden_iff => Physics.CyclicBasisDipoleSelection.selected_forbidden_iff
]

assert_compatible GUT.CyclicBasisDipoleSelection.matrixUnit => Physics.CyclicBasisDipoleSelection.matrixUnit
assert_compatible GUT.CyclicBasisDipoleSelection.matrixUnit.eq_1 => Physics.CyclicBasisDipoleSelection.matrixUnit.eq_1
assert_compatible GUT.CyclicBasisDipoleSelection.matrixUnit_selected => Physics.CyclicBasisDipoleSelection.matrixUnit_selected
assert_compatible GUT.CyclicBasisDipoleSelection.selected_allowed_iff => Physics.CyclicBasisDipoleSelection.selected_allowed_iff
assert_compatible GUT.CyclicBasisDipoleSelection.selected_forbidden_iff => Physics.CyclicBasisDipoleSelection.selected_forbidden_iff
