import Physics.StandardModel.Operators.BaryonOne.Qque.MixedQqueCyclicNecessity
import Physics.StandardModel.Operators.FlavoredCyclicSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.MixedQqueCyclicNecessity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.MixedQqueCyclicNecessity.controlCharges => Physics.MixedQqueCyclicNecessity.controlCharges,
  GUT.MixedQqueCyclicNecessity.controlE => Physics.MixedQqueCyclicNecessity.controlE,
  GUT.MixedQqueCyclicNecessity.controlE.eq_1 => Physics.MixedQqueCyclicNecessity.controlE.eq_1,
  GUT.MixedQqueCyclicNecessity.controlQ => Physics.MixedQqueCyclicNecessity.controlQ,
  GUT.MixedQqueCyclicNecessity.controlU => Physics.MixedQqueCyclicNecessity.controlU,
  GUT.MixedQqueCyclicNecessity.controlU.eq_1 => Physics.MixedQqueCyclicNecessity.controlU.eq_1,
  GUT.MixedQqueCyclicNecessity.control_allowed => Physics.MixedQqueCyclicNecessity.control_allowed,
  GUT.MixedQqueCyclicNecessity.control_diagonal_passes => Physics.MixedQqueCyclicNecessity.control_diagonal_passes,
  GUT.MixedQqueCyclicNecessity.control_mixed_neutral => Physics.MixedQqueCyclicNecessity.control_mixed_neutral,
  GUT.MixedQqueCyclicNecessity.control_not_forbidden => Physics.MixedQqueCyclicNecessity.control_not_forbidden,
  GUT.MixedQqueCyclicNecessity.control_total_allowed => Physics.MixedQqueCyclicNecessity.control_total_allowed,
  GUT.MixedQqueCyclicNecessity.necessary => Physics.MixedQqueCyclicNecessity.necessary,
  GUT.MixedQqueCyclicNecessity.neutral_pair_allowed => Physics.MixedQqueCyclicNecessity.neutral_pair_allowed,
  GUT.MixedQqueCyclicNecessity.pair_charge => Physics.MixedQqueCyclicNecessity.pair_charge,
  GUT.MixedQqueCyclicNecessity.total_necessary => Physics.MixedQqueCyclicNecessity.total_necessary
]

assert_compatible GUT.MixedQqueCyclicNecessity.controlCharges => Physics.MixedQqueCyclicNecessity.controlCharges
assert_compatible GUT.MixedQqueCyclicNecessity.controlE => Physics.MixedQqueCyclicNecessity.controlE
assert_compatible GUT.MixedQqueCyclicNecessity.controlE.eq_1 => Physics.MixedQqueCyclicNecessity.controlE.eq_1
assert_compatible GUT.MixedQqueCyclicNecessity.controlQ => Physics.MixedQqueCyclicNecessity.controlQ
assert_compatible GUT.MixedQqueCyclicNecessity.controlU => Physics.MixedQqueCyclicNecessity.controlU
assert_compatible GUT.MixedQqueCyclicNecessity.controlU.eq_1 => Physics.MixedQqueCyclicNecessity.controlU.eq_1
assert_compatible GUT.MixedQqueCyclicNecessity.control_allowed => Physics.MixedQqueCyclicNecessity.control_allowed
assert_compatible GUT.MixedQqueCyclicNecessity.control_diagonal_passes => Physics.MixedQqueCyclicNecessity.control_diagonal_passes
assert_compatible GUT.MixedQqueCyclicNecessity.control_mixed_neutral => Physics.MixedQqueCyclicNecessity.control_mixed_neutral
assert_compatible GUT.MixedQqueCyclicNecessity.control_not_forbidden => Physics.MixedQqueCyclicNecessity.control_not_forbidden
assert_compatible GUT.MixedQqueCyclicNecessity.control_total_allowed => Physics.MixedQqueCyclicNecessity.control_total_allowed
assert_compatible GUT.MixedQqueCyclicNecessity.necessary => Physics.MixedQqueCyclicNecessity.necessary
assert_compatible GUT.MixedQqueCyclicNecessity.neutral_pair_allowed => Physics.MixedQqueCyclicNecessity.neutral_pair_allowed
assert_compatible GUT.MixedQqueCyclicNecessity.pair_charge => Physics.MixedQqueCyclicNecessity.pair_charge
assert_compatible GUT.MixedQqueCyclicNecessity.total_necessary => Physics.MixedQqueCyclicNecessity.total_necessary
