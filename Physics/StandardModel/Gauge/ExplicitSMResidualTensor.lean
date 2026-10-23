import Physics.StandardModel.Gauge.Tensors.ExplicitSMResidualTensor
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.RepresentationTheory.ExternalInvariantTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.ExplicitSMResidualTensor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExplicitSMResidualTensor.exists_on_fields => Physics.ExplicitSMResidualTensor.exists_on_fields,
  GUT.ExplicitSMResidualTensor.fields => Physics.ExplicitSMResidualTensor.fields,
  GUT.ExplicitSMResidualTensor.multiplicity => Physics.ExplicitSMResidualTensor.multiplicity,
  GUT.ExplicitSMResidualTensor.qque => Physics.ExplicitSMResidualTensor.qque,
  GUT.ExplicitSMResidualTensor.qque_ne_zero => Physics.ExplicitSMResidualTensor.qque_ne_zero,
  GUT.ExplicitSMResidualTensor.qque_ne_zero_iff => Physics.ExplicitSMResidualTensor.qque_ne_zero_iff,
  GUT.ExplicitSMResidualTensor.qque_tmul => Physics.ExplicitSMResidualTensor.qque_tmul,
  GUT.ExplicitSMResidualTensor.qque_zero => Physics.ExplicitSMResidualTensor.qque_zero
]

assert_compatible GUT.ExplicitSMResidualTensor.exists_on_fields => Physics.ExplicitSMResidualTensor.exists_on_fields
assert_compatible GUT.ExplicitSMResidualTensor.fields => Physics.ExplicitSMResidualTensor.fields
assert_compatible GUT.ExplicitSMResidualTensor.multiplicity => Physics.ExplicitSMResidualTensor.multiplicity
assert_compatible GUT.ExplicitSMResidualTensor.qque => Physics.ExplicitSMResidualTensor.qque
assert_compatible GUT.ExplicitSMResidualTensor.qque_ne_zero => Physics.ExplicitSMResidualTensor.qque_ne_zero
assert_compatible GUT.ExplicitSMResidualTensor.qque_ne_zero_iff => Physics.ExplicitSMResidualTensor.qque_ne_zero_iff
assert_compatible GUT.ExplicitSMResidualTensor.qque_tmul => Physics.ExplicitSMResidualTensor.qque_tmul
assert_compatible GUT.ExplicitSMResidualTensor.qque_zero => Physics.ExplicitSMResidualTensor.qque_zero
