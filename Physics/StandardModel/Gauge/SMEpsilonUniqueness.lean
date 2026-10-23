import Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness
import Physics.StandardModel.Gauge.SMEpsilonTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.SMEpsilonUniqueness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMEpsilonUniqueness.color_basis_vanish => Physics.SMEpsilonUniqueness.color_basis_vanish,
  GUT.SMEpsilonUniqueness.color_unique => Physics.SMEpsilonUniqueness.color_unique,
  GUT.SMEpsilonUniqueness.weak_unique => Physics.SMEpsilonUniqueness.weak_unique
]

assert_compatible GUT.SMEpsilonUniqueness.color_basis_vanish => Physics.SMEpsilonUniqueness.color_basis_vanish
assert_compatible GUT.SMEpsilonUniqueness.color_unique => Physics.SMEpsilonUniqueness.color_unique
assert_compatible GUT.SMEpsilonUniqueness.weak_unique => Physics.SMEpsilonUniqueness.weak_unique
