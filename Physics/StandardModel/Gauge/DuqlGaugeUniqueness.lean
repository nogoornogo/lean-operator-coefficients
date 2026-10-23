import Physics.StandardModel.Gauge.Tensors.DuqlGaugeUniqueness
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.DuqlGaugeUniqueness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuqlGaugeUniqueness.Coefficient => Physics.DuqlGaugeUniqueness.Coefficient,
  GUT.DuqlGaugeUniqueness.colorSlice => Physics.DuqlGaugeUniqueness.colorSlice,
  GUT.DuqlGaugeUniqueness.colorSlice.eq_1 => Physics.DuqlGaugeUniqueness.colorSlice.eq_1,
  GUT.DuqlGaugeUniqueness.colorSlice_invariant => Physics.DuqlGaugeUniqueness.colorSlice_invariant,
  GUT.DuqlGaugeUniqueness.unique => Physics.DuqlGaugeUniqueness.unique,
  GUT.DuqlGaugeUniqueness.weakSlice => Physics.DuqlGaugeUniqueness.weakSlice,
  GUT.DuqlGaugeUniqueness.weakSlice.eq_1 => Physics.DuqlGaugeUniqueness.weakSlice.eq_1,
  GUT.DuqlGaugeUniqueness.weakSlice_invariant => Physics.DuqlGaugeUniqueness.weakSlice_invariant
]

assert_compatible GUT.DuqlGaugeUniqueness.Coefficient => Physics.DuqlGaugeUniqueness.Coefficient
assert_compatible GUT.DuqlGaugeUniqueness.colorSlice => Physics.DuqlGaugeUniqueness.colorSlice
assert_compatible GUT.DuqlGaugeUniqueness.colorSlice.eq_1 => Physics.DuqlGaugeUniqueness.colorSlice.eq_1
assert_compatible GUT.DuqlGaugeUniqueness.colorSlice_invariant => Physics.DuqlGaugeUniqueness.colorSlice_invariant
assert_compatible GUT.DuqlGaugeUniqueness.unique => Physics.DuqlGaugeUniqueness.unique
assert_compatible GUT.DuqlGaugeUniqueness.weakSlice => Physics.DuqlGaugeUniqueness.weakSlice
assert_compatible GUT.DuqlGaugeUniqueness.weakSlice.eq_1 => Physics.DuqlGaugeUniqueness.weakSlice.eq_1
assert_compatible GUT.DuqlGaugeUniqueness.weakSlice_invariant => Physics.DuqlGaugeUniqueness.weakSlice_invariant
