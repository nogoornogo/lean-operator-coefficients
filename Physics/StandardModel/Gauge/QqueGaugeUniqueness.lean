import Physics.StandardModel.Gauge.Tensors.QqueGaugeUniqueness
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.QqueGaugeUniqueness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueGaugeUniqueness.Coefficient => Physics.QqueGaugeUniqueness.Coefficient,
  GUT.QqueGaugeUniqueness.colorSlice => Physics.QqueGaugeUniqueness.colorSlice,
  GUT.QqueGaugeUniqueness.colorSlice.eq_1 => Physics.QqueGaugeUniqueness.colorSlice.eq_1,
  GUT.QqueGaugeUniqueness.colorSlice_invariant => Physics.QqueGaugeUniqueness.colorSlice_invariant,
  GUT.QqueGaugeUniqueness.eq_smul_qque => Physics.QqueGaugeUniqueness.eq_smul_qque,
  GUT.QqueGaugeUniqueness.weakSlice => Physics.QqueGaugeUniqueness.weakSlice,
  GUT.QqueGaugeUniqueness.weakSlice.eq_1 => Physics.QqueGaugeUniqueness.weakSlice.eq_1,
  GUT.QqueGaugeUniqueness.weakSlice_invariant => Physics.QqueGaugeUniqueness.weakSlice_invariant
]

assert_compatible GUT.QqueGaugeUniqueness.Coefficient => Physics.QqueGaugeUniqueness.Coefficient
assert_compatible GUT.QqueGaugeUniqueness.colorSlice => Physics.QqueGaugeUniqueness.colorSlice
assert_compatible GUT.QqueGaugeUniqueness.colorSlice.eq_1 => Physics.QqueGaugeUniqueness.colorSlice.eq_1
assert_compatible GUT.QqueGaugeUniqueness.colorSlice_invariant => Physics.QqueGaugeUniqueness.colorSlice_invariant
assert_compatible GUT.QqueGaugeUniqueness.eq_smul_qque => Physics.QqueGaugeUniqueness.eq_smul_qque
assert_compatible GUT.QqueGaugeUniqueness.weakSlice => Physics.QqueGaugeUniqueness.weakSlice
assert_compatible GUT.QqueGaugeUniqueness.weakSlice.eq_1 => Physics.QqueGaugeUniqueness.weakSlice.eq_1
assert_compatible GUT.QqueGaugeUniqueness.weakSlice_invariant => Physics.QqueGaugeUniqueness.weakSlice_invariant
