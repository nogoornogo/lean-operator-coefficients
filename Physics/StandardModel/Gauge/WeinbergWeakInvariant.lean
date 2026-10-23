import Physics.StandardModel.Gauge.Tensors.WeinbergWeakInvariant
import Physics.StandardModel.Gauge.DipoleGaugeTensor
import Math.RepresentationTheory.TwoComponentSymmetricSquare
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.WeinbergWeakInvariant instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleGaugeTensor.adjoint.eq_1 => Physics.DipoleGaugeTensor.adjoint.eq_1,
  GUT.DipoleGaugeTensor.weak.eq_1 => Physics.DipoleGaugeTensor.weak.eq_1,
  GUT.WeinbergWeakInvariant.Coefficient => Physics.WeinbergWeakInvariant.Coefficient,
  GUT.WeinbergWeakInvariant.contraction => Physics.WeinbergWeakInvariant.contraction,
  GUT.WeinbergWeakInvariant.contraction_apply => Physics.WeinbergWeakInvariant.contraction_apply,
  GUT.WeinbergWeakInvariant.contraction_witness => Physics.WeinbergWeakInvariant.contraction_witness,
  GUT.WeinbergWeakInvariant.coordinateEquiv => Physics.WeinbergWeakInvariant.coordinateEquiv,
  GUT.WeinbergWeakInvariant.diagonal_apply => Physics.WeinbergWeakInvariant.diagonal_apply,
  GUT.WeinbergWeakInvariant.domain => Physics.WeinbergWeakInvariant.domain,
  GUT.WeinbergWeakInvariant.domainEquiv => Physics.WeinbergWeakInvariant.domainEquiv,
  GUT.WeinbergWeakInvariant.higgsDualEquiv => Physics.WeinbergWeakInvariant.higgsDualEquiv,
  GUT.WeinbergWeakInvariant.unique => Physics.WeinbergWeakInvariant.unique,
  GUT.WeinbergWeakInvariant.witness => Physics.WeinbergWeakInvariant.witness,
  GUT.WeinbergWeakInvariant.witness.eq_1 => Physics.WeinbergWeakInvariant.witness.eq_1
]

assert_compatible GUT.DipoleGaugeTensor.adjoint.eq_1 => Physics.DipoleGaugeTensor.adjoint.eq_1
assert_compatible GUT.DipoleGaugeTensor.weak.eq_1 => Physics.DipoleGaugeTensor.weak.eq_1
assert_compatible GUT.WeinbergWeakInvariant.Coefficient => Physics.WeinbergWeakInvariant.Coefficient
assert_compatible GUT.WeinbergWeakInvariant.contraction => Physics.WeinbergWeakInvariant.contraction
assert_compatible GUT.WeinbergWeakInvariant.contraction_apply => Physics.WeinbergWeakInvariant.contraction_apply
assert_compatible GUT.WeinbergWeakInvariant.contraction_witness => Physics.WeinbergWeakInvariant.contraction_witness
assert_compatible GUT.WeinbergWeakInvariant.coordinateEquiv => Physics.WeinbergWeakInvariant.coordinateEquiv
assert_compatible GUT.WeinbergWeakInvariant.diagonal_apply => Physics.WeinbergWeakInvariant.diagonal_apply
assert_compatible GUT.WeinbergWeakInvariant.domain => Physics.WeinbergWeakInvariant.domain
assert_compatible GUT.WeinbergWeakInvariant.domainEquiv => Physics.WeinbergWeakInvariant.domainEquiv
assert_compatible GUT.WeinbergWeakInvariant.higgsDualEquiv => Physics.WeinbergWeakInvariant.higgsDualEquiv
assert_compatible GUT.WeinbergWeakInvariant.unique => Physics.WeinbergWeakInvariant.unique
assert_compatible GUT.WeinbergWeakInvariant.witness => Physics.WeinbergWeakInvariant.witness
assert_compatible GUT.WeinbergWeakInvariant.witness.eq_1 => Physics.WeinbergWeakInvariant.witness.eq_1
