import Physics.StandardModel.Operators.Dipole.SemisimpleDipoleSelection
import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.SemisimpleDipoleSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SemisimpleDipoleSelection.coordinates => Physics.SemisimpleDipoleSelection.coordinates,
  GUT.SemisimpleDipoleSelection.coordinates.congr_simp => Physics.SemisimpleDipoleSelection.coordinates.congr_simp,
  GUT.SemisimpleDipoleSelection.expansion => Physics.SemisimpleDipoleSelection.expansion,
  GUT.SemisimpleDipoleSelection.homTransport => Physics.SemisimpleDipoleSelection.homTransport,
  GUT.SemisimpleDipoleSelection.matrixUnit => Physics.SemisimpleDipoleSelection.matrixUnit,
  GUT.SemisimpleDipoleSelection.matrixUnit.congr_simp => Physics.SemisimpleDipoleSelection.matrixUnit.congr_simp,
  GUT.SemisimpleDipoleSelection.matrixUnit.eq_1 => Physics.SemisimpleDipoleSelection.matrixUnit.eq_1,
  GUT.SemisimpleDipoleSelection.selected_allowed_iff => Physics.SemisimpleDipoleSelection.selected_allowed_iff,
  GUT.SemisimpleDipoleSelection.selected_forbidden_iff => Physics.SemisimpleDipoleSelection.selected_forbidden_iff
]

assert_compatible GUT.SemisimpleDipoleSelection.coordinates => Physics.SemisimpleDipoleSelection.coordinates
assert_compatible GUT.SemisimpleDipoleSelection.coordinates.congr_simp => Physics.SemisimpleDipoleSelection.coordinates.congr_simp
assert_compatible GUT.SemisimpleDipoleSelection.expansion => Physics.SemisimpleDipoleSelection.expansion
assert_compatible GUT.SemisimpleDipoleSelection.homTransport => Physics.SemisimpleDipoleSelection.homTransport
assert_compatible GUT.SemisimpleDipoleSelection.matrixUnit => Physics.SemisimpleDipoleSelection.matrixUnit
assert_compatible GUT.SemisimpleDipoleSelection.matrixUnit.congr_simp => Physics.SemisimpleDipoleSelection.matrixUnit.congr_simp
assert_compatible GUT.SemisimpleDipoleSelection.matrixUnit.eq_1 => Physics.SemisimpleDipoleSelection.matrixUnit.eq_1
assert_compatible GUT.SemisimpleDipoleSelection.selected_allowed_iff => Physics.SemisimpleDipoleSelection.selected_allowed_iff
assert_compatible GUT.SemisimpleDipoleSelection.selected_forbidden_iff => Physics.SemisimpleDipoleSelection.selected_forbidden_iff
