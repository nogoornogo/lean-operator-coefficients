import Physics.FieldTheory.Jets.Lorentz.LorentzFiniteControls
import Physics.FieldTheory.Jets.LorentzJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lorentz.LorentzFiniteControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LorentzFiniteControls.E => Physics.LorentzFiniteControls.E,
  GUT.LorentzFiniteControls.diagonals => Physics.LorentzFiniteControls.diagonals,
  GUT.LorentzFiniteControls.flipX => Physics.LorentzFiniteControls.flipX,
  GUT.LorentzFiniteControls.flipX_direction => Physics.LorentzFiniteControls.flipX_direction,
  GUT.LorentzFiniteControls.flipX_inverse => Physics.LorentzFiniteControls.flipX_inverse,
  GUT.LorentzFiniteControls.flipZ => Physics.LorentzFiniteControls.flipZ,
  GUT.LorentzFiniteControls.flipZ_direction => Physics.LorentzFiniteControls.flipZ_direction,
  GUT.LorentzFiniteControls.flipZ_inverse => Physics.LorentzFiniteControls.flipZ_inverse,
  GUT.LorentzFiniteControls.imagRows => Physics.LorentzFiniteControls.imagRows,
  GUT.LorentzFiniteControls.imagRows.eq_1 => Physics.LorentzFiniteControls.imagRows.eq_1,
  GUT.LorentzFiniteControls.imag_basis => Physics.LorentzFiniteControls.imag_basis,
  GUT.LorentzFiniteControls.imag_direction => Physics.LorentzFiniteControls.imag_direction,
  GUT.LorentzFiniteControls.minusX => Physics.LorentzFiniteControls.minusX,
  GUT.LorentzFiniteControls.minusX.eq_1 => Physics.LorentzFiniteControls.minusX.eq_1,
  GUT.LorentzFiniteControls.minusZ => Physics.LorentzFiniteControls.minusZ,
  GUT.LorentzFiniteControls.minusZ.eq_1 => Physics.LorentzFiniteControls.minusZ.eq_1,
  GUT.LorentzFiniteControls.offdiagonal => Physics.LorentzFiniteControls.offdiagonal,
  GUT.LorentzFiniteControls.realRows => Physics.LorentzFiniteControls.realRows,
  GUT.LorentzFiniteControls.realRows.eq_1 => Physics.LorentzFiniteControls.realRows.eq_1,
  GUT.LorentzFiniteControls.real_basis => Physics.LorentzFiniteControls.real_basis,
  GUT.LorentzFiniteControls.real_direction => Physics.LorentzFiniteControls.real_direction,
  GUT.LorentzFiniteControls.shear => Physics.LorentzFiniteControls.shear,
  GUT.LorentzFiniteControls.shear.eq_1 => Physics.LorentzFiniteControls.shear.eq_1,
  GUT.LorentzFiniteControls.shear_inverse => Physics.LorentzFiniteControls.shear_inverse,
  GUT.LorentzFiniteControls.signsX => Physics.LorentzFiniteControls.signsX,
  GUT.LorentzFiniteControls.signsX.eq_1 => Physics.LorentzFiniteControls.signsX.eq_1,
  GUT.LorentzFiniteControls.signsZ => Physics.LorentzFiniteControls.signsZ,
  GUT.LorentzFiniteControls.signsZ.eq_1 => Physics.LorentzFiniteControls.signsZ.eq_1,
  GUT.LorentzFiniteControls.trace_zero => Physics.LorentzFiniteControls.trace_zero,
  GUT.LorentzFiniteControls.vector_apply => Physics.LorentzFiniteControls.vector_apply
]

assert_compatible GUT.LorentzFiniteControls.E => Physics.LorentzFiniteControls.E
assert_compatible GUT.LorentzFiniteControls.diagonals => Physics.LorentzFiniteControls.diagonals
assert_compatible GUT.LorentzFiniteControls.flipX => Physics.LorentzFiniteControls.flipX
assert_compatible GUT.LorentzFiniteControls.flipX_direction => Physics.LorentzFiniteControls.flipX_direction
assert_compatible GUT.LorentzFiniteControls.flipX_inverse => Physics.LorentzFiniteControls.flipX_inverse
assert_compatible GUT.LorentzFiniteControls.flipZ => Physics.LorentzFiniteControls.flipZ
assert_compatible GUT.LorentzFiniteControls.flipZ_direction => Physics.LorentzFiniteControls.flipZ_direction
assert_compatible GUT.LorentzFiniteControls.flipZ_inverse => Physics.LorentzFiniteControls.flipZ_inverse
assert_compatible GUT.LorentzFiniteControls.imagRows => Physics.LorentzFiniteControls.imagRows
assert_compatible GUT.LorentzFiniteControls.imagRows.eq_1 => Physics.LorentzFiniteControls.imagRows.eq_1
assert_compatible GUT.LorentzFiniteControls.imag_basis => Physics.LorentzFiniteControls.imag_basis
assert_compatible GUT.LorentzFiniteControls.imag_direction => Physics.LorentzFiniteControls.imag_direction
assert_compatible GUT.LorentzFiniteControls.minusX => Physics.LorentzFiniteControls.minusX
assert_compatible GUT.LorentzFiniteControls.minusX.eq_1 => Physics.LorentzFiniteControls.minusX.eq_1
assert_compatible GUT.LorentzFiniteControls.minusZ => Physics.LorentzFiniteControls.minusZ
assert_compatible GUT.LorentzFiniteControls.minusZ.eq_1 => Physics.LorentzFiniteControls.minusZ.eq_1
assert_compatible GUT.LorentzFiniteControls.offdiagonal => Physics.LorentzFiniteControls.offdiagonal
assert_compatible GUT.LorentzFiniteControls.realRows => Physics.LorentzFiniteControls.realRows
assert_compatible GUT.LorentzFiniteControls.realRows.eq_1 => Physics.LorentzFiniteControls.realRows.eq_1
assert_compatible GUT.LorentzFiniteControls.real_basis => Physics.LorentzFiniteControls.real_basis
assert_compatible GUT.LorentzFiniteControls.real_direction => Physics.LorentzFiniteControls.real_direction
assert_compatible GUT.LorentzFiniteControls.shear => Physics.LorentzFiniteControls.shear
assert_compatible GUT.LorentzFiniteControls.shear.eq_1 => Physics.LorentzFiniteControls.shear.eq_1
assert_compatible GUT.LorentzFiniteControls.shear_inverse => Physics.LorentzFiniteControls.shear_inverse
assert_compatible GUT.LorentzFiniteControls.signsX => Physics.LorentzFiniteControls.signsX
assert_compatible GUT.LorentzFiniteControls.signsX.eq_1 => Physics.LorentzFiniteControls.signsX.eq_1
assert_compatible GUT.LorentzFiniteControls.signsZ => Physics.LorentzFiniteControls.signsZ
assert_compatible GUT.LorentzFiniteControls.signsZ.eq_1 => Physics.LorentzFiniteControls.signsZ.eq_1
assert_compatible GUT.LorentzFiniteControls.trace_zero => Physics.LorentzFiniteControls.trace_zero
assert_compatible GUT.LorentzFiniteControls.vector_apply => Physics.LorentzFiniteControls.vector_apply
