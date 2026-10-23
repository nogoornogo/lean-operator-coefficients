import Physics.StandardModel.Gauge.Tensors.ExteriorPairing
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.ExteriorPairing instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StandardSMExterior.color_pair_invariant => Physics.StandardSMExterior.color_pair_invariant,
  GUT.StandardSMExterior.mixed_pair_covariant => Physics.StandardSMExterior.mixed_pair_covariant,
  GUT.StandardSMExterior.weak_pair_invariant => Physics.StandardSMExterior.weak_pair_invariant
]

assert_compatible GUT.StandardSMExterior.color_pair_invariant => Physics.StandardSMExterior.color_pair_invariant
assert_compatible GUT.StandardSMExterior.mixed_pair_covariant => Physics.StandardSMExterior.mixed_pair_covariant
assert_compatible GUT.StandardSMExterior.weak_pair_invariant => Physics.StandardSMExterior.weak_pair_invariant
