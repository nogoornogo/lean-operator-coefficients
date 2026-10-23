import Physics.StandardModel.Gauge.Tensors.ResidualGaugeTensor
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Physics.StandardModel.Operators.AbelianProtonCharacter
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.ResidualGaugeTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StandardSMResidualTensor.charged => Physics.StandardSMResidualTensor.charged,
  GUT.StandardSMResidualTensor.charged.eq_1 => Physics.StandardSMResidualTensor.charged.eq_1,
  GUT.StandardSMResidualTensor.duqlIntertwiner => Physics.StandardSMResidualTensor.duqlIntertwiner,
  GUT.StandardSMResidualTensor.duqlRepresentation => Physics.StandardSMResidualTensor.duqlRepresentation,
  GUT.StandardSMResidualTensor.duqlRepresentation.eq_1 => Physics.StandardSMResidualTensor.duqlRepresentation.eq_1,
  GUT.StandardSMResidualTensor.duqlRepresentation_eq => Physics.StandardSMResidualTensor.duqlRepresentation_eq,
  GUT.StandardSMResidualTensor.duql_covariant => Physics.StandardSMResidualTensor.duql_covariant,
  GUT.StandardSMResidualTensor.duql_invariant_iff => Physics.StandardSMResidualTensor.duql_invariant_iff,
  GUT.StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible => Physics.StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible,
  GUT.StandardSMResidualTensor.qqueIntertwiner => Physics.StandardSMResidualTensor.qqueIntertwiner,
  GUT.StandardSMResidualTensor.qqueRepresentation => Physics.StandardSMResidualTensor.qqueRepresentation,
  GUT.StandardSMResidualTensor.qqueRepresentation.eq_1 => Physics.StandardSMResidualTensor.qqueRepresentation.eq_1,
  GUT.StandardSMResidualTensor.qqueRepresentation_eq => Physics.StandardSMResidualTensor.qqueRepresentation_eq,
  GUT.StandardSMResidualTensor.qque_covariant => Physics.StandardSMResidualTensor.qque_covariant,
  GUT.StandardSMResidualTensor.qque_invariant_iff => Physics.StandardSMResidualTensor.qque_invariant_iff
]

assert_compatible GUT.StandardSMResidualTensor.charged => Physics.StandardSMResidualTensor.charged
assert_compatible GUT.StandardSMResidualTensor.charged.eq_1 => Physics.StandardSMResidualTensor.charged.eq_1
assert_compatible GUT.StandardSMResidualTensor.duqlIntertwiner => Physics.StandardSMResidualTensor.duqlIntertwiner
assert_compatible GUT.StandardSMResidualTensor.duqlRepresentation => Physics.StandardSMResidualTensor.duqlRepresentation
assert_compatible GUT.StandardSMResidualTensor.duqlRepresentation.eq_1 => Physics.StandardSMResidualTensor.duqlRepresentation.eq_1
assert_compatible GUT.StandardSMResidualTensor.duqlRepresentation_eq => Physics.StandardSMResidualTensor.duqlRepresentation_eq
assert_compatible GUT.StandardSMResidualTensor.duql_covariant => Physics.StandardSMResidualTensor.duql_covariant
assert_compatible GUT.StandardSMResidualTensor.duql_invariant_iff => Physics.StandardSMResidualTensor.duql_invariant_iff
assert_compatible GUT.StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible => Physics.StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible
assert_compatible GUT.StandardSMResidualTensor.qqueIntertwiner => Physics.StandardSMResidualTensor.qqueIntertwiner
assert_compatible GUT.StandardSMResidualTensor.qqueRepresentation => Physics.StandardSMResidualTensor.qqueRepresentation
assert_compatible GUT.StandardSMResidualTensor.qqueRepresentation.eq_1 => Physics.StandardSMResidualTensor.qqueRepresentation.eq_1
assert_compatible GUT.StandardSMResidualTensor.qqueRepresentation_eq => Physics.StandardSMResidualTensor.qqueRepresentation_eq
assert_compatible GUT.StandardSMResidualTensor.qque_covariant => Physics.StandardSMResidualTensor.qque_covariant
assert_compatible GUT.StandardSMResidualTensor.qque_invariant_iff => Physics.StandardSMResidualTensor.qque_invariant_iff
