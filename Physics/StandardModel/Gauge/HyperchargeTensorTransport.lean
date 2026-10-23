import Physics.StandardModel.Gauge.Charges.HyperchargeTensorTransport
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.RepresentationTheory.ExternalInvariantTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Charges.HyperchargeTensorTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HyperchargeTensorTransport.dualLine => Physics.HyperchargeTensorTransport.dualLine,
  GUT.HyperchargeTensorTransport.five => Physics.HyperchargeTensorTransport.five,
  GUT.HyperchargeTensorTransport.fiveNeutral => Physics.HyperchargeTensorTransport.fiveNeutral,
  GUT.HyperchargeTensorTransport.four => Physics.HyperchargeTensorTransport.four,
  GUT.HyperchargeTensorTransport.neutral => Physics.HyperchargeTensorTransport.neutral,
  GUT.HyperchargeTensorTransport.neutralOfEq => Physics.HyperchargeTensorTransport.neutralOfEq,
  GUT.HyperchargeTensorTransport.phase_add => Physics.HyperchargeTensorTransport.phase_add,
  GUT.HyperchargeTensorTransport.phase_inv => Physics.HyperchargeTensorTransport.phase_inv,
  GUT.HyperchargeTensorTransport.tensor => Physics.HyperchargeTensorTransport.tensor
]

assert_compatible GUT.HyperchargeTensorTransport.dualLine => Physics.HyperchargeTensorTransport.dualLine
assert_compatible GUT.HyperchargeTensorTransport.five => Physics.HyperchargeTensorTransport.five
assert_compatible GUT.HyperchargeTensorTransport.fiveNeutral => Physics.HyperchargeTensorTransport.fiveNeutral
assert_compatible GUT.HyperchargeTensorTransport.four => Physics.HyperchargeTensorTransport.four
assert_compatible GUT.HyperchargeTensorTransport.neutral => Physics.HyperchargeTensorTransport.neutral
assert_compatible GUT.HyperchargeTensorTransport.neutralOfEq => Physics.HyperchargeTensorTransport.neutralOfEq
assert_compatible GUT.HyperchargeTensorTransport.phase_add => Physics.HyperchargeTensorTransport.phase_add
assert_compatible GUT.HyperchargeTensorTransport.phase_inv => Physics.HyperchargeTensorTransport.phase_inv
assert_compatible GUT.HyperchargeTensorTransport.tensor => Physics.HyperchargeTensorTransport.tensor
