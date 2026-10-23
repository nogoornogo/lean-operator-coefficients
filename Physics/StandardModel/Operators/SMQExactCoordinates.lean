import Physics.StandardModel.Operators.Support.Quark.SMQExactCoordinates
import Physics.StandardModel.Operators.SMRationalLocalKernel
import Physics.StandardModel.Operators.SMConstantContentRanks
import Physics.StandardModel.Operators.SMWeakWeightBasis
import Math.LinearAlgebra.ExactPowerCoordinates
import Math.RepresentationTheory.ConstantExteriorAction
import Physics.StandardModel.Operators.SMGaussianLocalData
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQExactCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQExactCoordinates.Index => Physics.SMQExactCoordinates.Index,
  GUT.SMQExactCoordinates.Slots => Physics.SMQExactCoordinates.Slots,
  GUT.SMQExactCoordinates.actionMatrix => Physics.SMQExactCoordinates.actionMatrix,
  GUT.SMQExactCoordinates.action_sample_coordinate => Physics.SMQExactCoordinates.action_sample_coordinate,
  GUT.SMQExactCoordinates.basis => Physics.SMQExactCoordinates.basis,
  GUT.SMQExactCoordinates.basis.eq_1 => Physics.SMQExactCoordinates.basis.eq_1,
  GUT.SMQExactCoordinates.basis_apply => Physics.SMQExactCoordinates.basis_apply,
  GUT.SMQExactCoordinates.basis_repr_pure => Physics.SMQExactCoordinates.basis_repr_pure,
  GUT.SMQExactCoordinates.bosonMatrix => Physics.SMQExactCoordinates.bosonMatrix,
  GUT.SMQExactCoordinates.bosonMatrix.eq_1 => Physics.SMQExactCoordinates.bosonMatrix.eq_1,
  GUT.SMQExactCoordinates.boson_sample_coordinate => Physics.SMQExactCoordinates.boson_sample_coordinate,
  GUT.SMQExactCoordinates.fieldBasis => Physics.SMQExactCoordinates.fieldBasis,
  GUT.SMQExactCoordinates.fieldMatrix => Physics.SMQExactCoordinates.fieldMatrix,
  GUT.SMQExactCoordinates.field_coordinate => Physics.SMQExactCoordinates.field_coordinate,
  GUT.SMQExactCoordinates.field_sample_coordinate => Physics.SMQExactCoordinates.field_sample_coordinate,
  GUT.SMQExactCoordinates.pattern => Physics.SMQExactCoordinates.pattern,
  GUT.SMQExactCoordinates.slotEquiv => Physics.SMQExactCoordinates.slotEquiv,
  GUT.SMQExactCoordinates.transport => Physics.SMQExactCoordinates.transport,
  GUT.SMQExactCoordinates.transport.eq_1 => Physics.SMQExactCoordinates.transport.eq_1
]

assert_compatible GUT.SMQExactCoordinates.Index => Physics.SMQExactCoordinates.Index
assert_compatible GUT.SMQExactCoordinates.Slots => Physics.SMQExactCoordinates.Slots
assert_compatible GUT.SMQExactCoordinates.actionMatrix => Physics.SMQExactCoordinates.actionMatrix
assert_compatible GUT.SMQExactCoordinates.action_sample_coordinate => Physics.SMQExactCoordinates.action_sample_coordinate
assert_compatible GUT.SMQExactCoordinates.basis => Physics.SMQExactCoordinates.basis
assert_compatible GUT.SMQExactCoordinates.basis.eq_1 => Physics.SMQExactCoordinates.basis.eq_1
assert_compatible GUT.SMQExactCoordinates.basis_apply => Physics.SMQExactCoordinates.basis_apply
assert_compatible GUT.SMQExactCoordinates.basis_repr_pure => Physics.SMQExactCoordinates.basis_repr_pure
assert_compatible GUT.SMQExactCoordinates.bosonMatrix => Physics.SMQExactCoordinates.bosonMatrix
assert_compatible GUT.SMQExactCoordinates.bosonMatrix.eq_1 => Physics.SMQExactCoordinates.bosonMatrix.eq_1
assert_compatible GUT.SMQExactCoordinates.boson_sample_coordinate => Physics.SMQExactCoordinates.boson_sample_coordinate
assert_compatible GUT.SMQExactCoordinates.fieldBasis => Physics.SMQExactCoordinates.fieldBasis
assert_compatible GUT.SMQExactCoordinates.fieldMatrix => Physics.SMQExactCoordinates.fieldMatrix
assert_compatible GUT.SMQExactCoordinates.field_coordinate => Physics.SMQExactCoordinates.field_coordinate
assert_compatible GUT.SMQExactCoordinates.field_sample_coordinate => Physics.SMQExactCoordinates.field_sample_coordinate
assert_compatible GUT.SMQExactCoordinates.pattern => Physics.SMQExactCoordinates.pattern
assert_compatible GUT.SMQExactCoordinates.slotEquiv => Physics.SMQExactCoordinates.slotEquiv
assert_compatible GUT.SMQExactCoordinates.transport => Physics.SMQExactCoordinates.transport
assert_compatible GUT.SMQExactCoordinates.transport.eq_1 => Physics.SMQExactCoordinates.transport.eq_1
