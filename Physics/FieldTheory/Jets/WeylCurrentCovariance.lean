import Physics.FieldTheory.Jets.Weyl.Equations.WeylCurrentCovariance
import Physics.FieldTheory.Jets.PairedWeylGeneratedInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylCurrentCovariance instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairedWeylInput.oddInc.eq_1 => Physics.PairedWeylInput.oddInc.eq_1,
  GUT.WeylCurrentCovariance.component => Physics.WeylCurrentCovariance.component,
  GUT.WeylCurrentCovariance.component.eq_1 => Physics.WeylCurrentCovariance.component.eq_1,
  GUT.WeylCurrentCovariance.current_covariant => Physics.WeylCurrentCovariance.current_covariant,
  GUT.WeylCurrentCovariance.current_dictionary => Physics.WeylCurrentCovariance.current_dictionary,
  GUT.WeylCurrentCovariance.field_components => Physics.WeylCurrentCovariance.field_components,
  GUT.WeylCurrentCovariance.instAddCommGroupA_physics => Physics.WeylCurrentCovariance.instAddCommGroupA_physics,
  GUT.WeylCurrentCovariance.instModuleComplexA_physics => Physics.WeylCurrentCovariance.instModuleComplexA_physics,
  GUT.WeylCurrentCovariance.instRingA_physics => Physics.WeylCurrentCovariance.instRingA_physics,
  GUT.WeylCurrentCovariance.matrixCurrent => Physics.WeylCurrentCovariance.matrixCurrent,
  GUT.WeylCurrentCovariance.matrix_covariant => Physics.WeylCurrentCovariance.matrix_covariant,
  GUT.WeylCurrentCovariance.psi_covariant => Physics.WeylCurrentCovariance.psi_covariant,
  GUT.WeylCurrentCovariance.vectorCurrent => Physics.WeylCurrentCovariance.vectorCurrent,
  GUT.WeylCurrentCovariance.vector_covariant => Physics.WeylCurrentCovariance.vector_covariant,
  GUT.WeylSpinor.conjugate.eq_1 => Physics.WeylSpinor.conjugate.eq_1,
  GUT.WeylSpinor.right.eq_1 => Physics.WeylSpinor.right.eq_1
]

assert_compatible GUT.PairedWeylInput.oddInc.eq_1 => Physics.PairedWeylInput.oddInc.eq_1
assert_compatible GUT.WeylCurrentCovariance.component => Physics.WeylCurrentCovariance.component
assert_compatible GUT.WeylCurrentCovariance.component.eq_1 => Physics.WeylCurrentCovariance.component.eq_1
assert_compatible GUT.WeylCurrentCovariance.current_covariant => Physics.WeylCurrentCovariance.current_covariant
assert_compatible GUT.WeylCurrentCovariance.current_dictionary => Physics.WeylCurrentCovariance.current_dictionary
assert_compatible GUT.WeylCurrentCovariance.field_components => Physics.WeylCurrentCovariance.field_components
assert_compatible GUT.WeylCurrentCovariance.instAddCommGroupA_physics => Physics.WeylCurrentCovariance.instAddCommGroupA_physics
assert_compatible GUT.WeylCurrentCovariance.instModuleComplexA_physics => Physics.WeylCurrentCovariance.instModuleComplexA_physics
assert_compatible GUT.WeylCurrentCovariance.instRingA_physics => Physics.WeylCurrentCovariance.instRingA_physics
assert_compatible GUT.WeylCurrentCovariance.matrixCurrent => Physics.WeylCurrentCovariance.matrixCurrent
assert_compatible GUT.WeylCurrentCovariance.matrix_covariant => Physics.WeylCurrentCovariance.matrix_covariant
assert_compatible GUT.WeylCurrentCovariance.psi_covariant => Physics.WeylCurrentCovariance.psi_covariant
assert_compatible GUT.WeylCurrentCovariance.vectorCurrent => Physics.WeylCurrentCovariance.vectorCurrent
assert_compatible GUT.WeylCurrentCovariance.vector_covariant => Physics.WeylCurrentCovariance.vector_covariant
assert_compatible GUT.WeylSpinor.conjugate.eq_1 => Physics.WeylSpinor.conjugate.eq_1
assert_compatible GUT.WeylSpinor.right.eq_1 => Physics.WeylSpinor.right.eq_1
