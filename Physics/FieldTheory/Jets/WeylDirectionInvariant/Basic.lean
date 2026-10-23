import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Basic
import Physics.FieldTheory.Jets.WeylCurrentCovariance
import Physics.FieldTheory.Jets.LorentzFiniteControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Basic instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylDirectionInvariant.Dir => Physics.WeylDirectionInvariant.Dir,
  GUT.WeylDirectionInvariant.S => Physics.WeylDirectionInvariant.S,
  GUT.WeylDirectionInvariant.Spin => Physics.WeylDirectionInvariant.Spin,
  GUT.WeylDirectionInvariant.Tensor => Physics.WeylDirectionInvariant.Tensor,
  GUT.WeylDirectionInvariant.component => Physics.WeylDirectionInvariant.component,
  GUT.WeylDirectionInvariant.component.eq_1 => Physics.WeylDirectionInvariant.component.eq_1,
  GUT.WeylDirectionInvariant.component_apply => Physics.WeylDirectionInvariant.component_apply,
  GUT.WeylDirectionInvariant.directionRows => Physics.WeylDirectionInvariant.directionRows,
  GUT.WeylDirectionInvariant.directionRows.eq_1 => Physics.WeylDirectionInvariant.directionRows.eq_1,
  GUT.WeylDirectionInvariant.direction_basis => Physics.WeylDirectionInvariant.direction_basis,
  GUT.WeylDirectionInvariant.kernel => Physics.WeylDirectionInvariant.kernel,
  GUT.WeylDirectionInvariant.row => Physics.WeylDirectionInvariant.row,
  GUT.WeylDirectionInvariant.sample => Physics.WeylDirectionInvariant.sample,
  GUT.WeylDirectionInvariant.sample.eq_1 => Physics.WeylDirectionInvariant.sample.eq_1,
  GUT.WeylDirectionInvariant.spinRows => Physics.WeylDirectionInvariant.spinRows,
  GUT.WeylDirectionInvariant.spin_basis => Physics.WeylDirectionInvariant.spin_basis
]

assert_compatible GUT.WeylDirectionInvariant.Dir => Physics.WeylDirectionInvariant.Dir
assert_compatible GUT.WeylDirectionInvariant.S => Physics.WeylDirectionInvariant.S
assert_compatible GUT.WeylDirectionInvariant.Spin => Physics.WeylDirectionInvariant.Spin
assert_compatible GUT.WeylDirectionInvariant.Tensor => Physics.WeylDirectionInvariant.Tensor
assert_compatible GUT.WeylDirectionInvariant.component => Physics.WeylDirectionInvariant.component
assert_compatible GUT.WeylDirectionInvariant.component.eq_1 => Physics.WeylDirectionInvariant.component.eq_1
assert_compatible GUT.WeylDirectionInvariant.component_apply => Physics.WeylDirectionInvariant.component_apply
assert_compatible GUT.WeylDirectionInvariant.directionRows => Physics.WeylDirectionInvariant.directionRows
assert_compatible GUT.WeylDirectionInvariant.directionRows.eq_1 => Physics.WeylDirectionInvariant.directionRows.eq_1
assert_compatible GUT.WeylDirectionInvariant.direction_basis => Physics.WeylDirectionInvariant.direction_basis
assert_compatible GUT.WeylDirectionInvariant.kernel => Physics.WeylDirectionInvariant.kernel
assert_compatible GUT.WeylDirectionInvariant.row => Physics.WeylDirectionInvariant.row
assert_compatible GUT.WeylDirectionInvariant.sample => Physics.WeylDirectionInvariant.sample
assert_compatible GUT.WeylDirectionInvariant.sample.eq_1 => Physics.WeylDirectionInvariant.sample.eq_1
assert_compatible GUT.WeylDirectionInvariant.spinRows => Physics.WeylDirectionInvariant.spinRows
assert_compatible GUT.WeylDirectionInvariant.spin_basis => Physics.WeylDirectionInvariant.spin_basis
