import Physics.StandardModel.Gauge.Tensors.DuueGaugeUniqueness
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.DuueGaugeUniqueness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DuueGaugeUniqueness.Coefficient => Physics.DuueGaugeUniqueness.Coefficient,
  GUT.DuueGaugeUniqueness.contraction => Physics.DuueGaugeUniqueness.contraction,
  GUT.DuueGaugeUniqueness.contraction.eq_1 => Physics.DuueGaugeUniqueness.contraction.eq_1,
  GUT.DuueGaugeUniqueness.contraction_apply => Physics.DuueGaugeUniqueness.contraction_apply,
  GUT.DuueGaugeUniqueness.intertwiner => Physics.DuueGaugeUniqueness.intertwiner,
  GUT.DuueGaugeUniqueness.intertwiner.eq_1 => Physics.DuueGaugeUniqueness.intertwiner.eq_1,
  GUT.DuueGaugeUniqueness.normalized => Physics.DuueGaugeUniqueness.normalized,
  GUT.DuueGaugeUniqueness.phases => Physics.DuueGaugeUniqueness.phases,
  GUT.DuueGaugeUniqueness.representation => Physics.DuueGaugeUniqueness.representation,
  GUT.DuueGaugeUniqueness.representation.eq_1 => Physics.DuueGaugeUniqueness.representation.eq_1,
  GUT.DuueGaugeUniqueness.slice => Physics.DuueGaugeUniqueness.slice,
  GUT.DuueGaugeUniqueness.slice.eq_1 => Physics.DuueGaugeUniqueness.slice.eq_1,
  GUT.DuueGaugeUniqueness.slice_invariant => Physics.DuueGaugeUniqueness.slice_invariant,
  GUT.DuueGaugeUniqueness.unique => Physics.DuueGaugeUniqueness.unique,
  GUT.DuueGaugeUniqueness.witness => Physics.DuueGaugeUniqueness.witness,
  GUT.DuueGaugeUniqueness.witness.eq_1 => Physics.DuueGaugeUniqueness.witness.eq_1
]

assert_compatible GUT.DuueGaugeUniqueness.Coefficient => Physics.DuueGaugeUniqueness.Coefficient
assert_compatible GUT.DuueGaugeUniqueness.contraction => Physics.DuueGaugeUniqueness.contraction
assert_compatible GUT.DuueGaugeUniqueness.contraction.eq_1 => Physics.DuueGaugeUniqueness.contraction.eq_1
assert_compatible GUT.DuueGaugeUniqueness.contraction_apply => Physics.DuueGaugeUniqueness.contraction_apply
assert_compatible GUT.DuueGaugeUniqueness.intertwiner => Physics.DuueGaugeUniqueness.intertwiner
assert_compatible GUT.DuueGaugeUniqueness.intertwiner.eq_1 => Physics.DuueGaugeUniqueness.intertwiner.eq_1
assert_compatible GUT.DuueGaugeUniqueness.normalized => Physics.DuueGaugeUniqueness.normalized
assert_compatible GUT.DuueGaugeUniqueness.phases => Physics.DuueGaugeUniqueness.phases
assert_compatible GUT.DuueGaugeUniqueness.representation => Physics.DuueGaugeUniqueness.representation
assert_compatible GUT.DuueGaugeUniqueness.representation.eq_1 => Physics.DuueGaugeUniqueness.representation.eq_1
assert_compatible GUT.DuueGaugeUniqueness.slice => Physics.DuueGaugeUniqueness.slice
assert_compatible GUT.DuueGaugeUniqueness.slice.eq_1 => Physics.DuueGaugeUniqueness.slice.eq_1
assert_compatible GUT.DuueGaugeUniqueness.slice_invariant => Physics.DuueGaugeUniqueness.slice_invariant
assert_compatible GUT.DuueGaugeUniqueness.unique => Physics.DuueGaugeUniqueness.unique
assert_compatible GUT.DuueGaugeUniqueness.witness => Physics.DuueGaugeUniqueness.witness
assert_compatible GUT.DuueGaugeUniqueness.witness.eq_1 => Physics.DuueGaugeUniqueness.witness.eq_1
