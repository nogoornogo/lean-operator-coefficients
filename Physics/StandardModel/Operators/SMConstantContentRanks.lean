import Physics.StandardModel.Operators.Support.Coordinates.SMConstantContentRanks
import Math.RepresentationTheory.ConstantPatternExterior
import Physics.StandardModel.Operators.SMChargedKernelRank
import Physics.StandardModel.Operators.LLHHKernelRank
import Physics.StandardModel.Operators.SMParityKernelRank
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMConstantContentRanks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMConstantContentRanks.above_capacity_rank => Physics.SMConstantContentRanks.above_capacity_rank,
  GUT.SMConstantContentRanks.actualRank => Physics.SMConstantContentRanks.actualRank,
  GUT.SMConstantContentRanks.carrier_dimension => Physics.SMConstantContentRanks.carrier_dimension,
  GUT.SMConstantContentRanks.charge => Physics.SMConstantContentRanks.charge,
  GUT.SMConstantContentRanks.charged_rank => Physics.SMConstantContentRanks.charged_rank,
  GUT.SMConstantContentRanks.columns => Physics.SMConstantContentRanks.columns,
  GUT.SMConstantContentRanks.columns.eq_1 => Physics.SMConstantContentRanks.columns.eq_1,
  GUT.SMConstantContentRanks.dimension => Physics.SMConstantContentRanks.dimension,
  GUT.SMConstantContentRanks.evaluate => Physics.SMConstantContentRanks.evaluate,
  GUT.SMConstantContentRanks.evaluate_sound => Physics.SMConstantContentRanks.evaluate_sound,
  GUT.SMConstantContentRanks.fieldFinite => Physics.SMConstantContentRanks.fieldFinite,
  GUT.SMConstantContentRanks.fixed_above => Physics.SMConstantContentRanks.fixed_above,
  GUT.SMConstantContentRanks.fixed_charged => Physics.SMConstantContentRanks.fixed_charged,
  GUT.SMConstantContentRanks.fixed_llhh => Physics.SMConstantContentRanks.fixed_llhh,
  GUT.SMConstantContentRanks.fixed_odd => Physics.SMConstantContentRanks.fixed_odd,
  GUT.SMConstantContentRanks.pattern => Physics.SMConstantContentRanks.pattern,
  GUT.SMConstantContentRanks.pattern.eq_1 => Physics.SMConstantContentRanks.pattern.eq_1,
  GUT.SMConstantContentRanks.source_dimension => Physics.SMConstantContentRanks.source_dimension,
  GUT.SMContentWeakBound.hypercharge.eq_1 => Physics.SMContentWeakBound.hypercharge.eq_1
]

assert_compatible GUT.SMConstantContentRanks.above_capacity_rank => Physics.SMConstantContentRanks.above_capacity_rank
assert_compatible GUT.SMConstantContentRanks.actualRank => Physics.SMConstantContentRanks.actualRank
assert_compatible GUT.SMConstantContentRanks.carrier_dimension => Physics.SMConstantContentRanks.carrier_dimension
assert_compatible GUT.SMConstantContentRanks.charge => Physics.SMConstantContentRanks.charge
assert_compatible GUT.SMConstantContentRanks.charged_rank => Physics.SMConstantContentRanks.charged_rank
assert_compatible GUT.SMConstantContentRanks.columns => Physics.SMConstantContentRanks.columns
assert_compatible GUT.SMConstantContentRanks.columns.eq_1 => Physics.SMConstantContentRanks.columns.eq_1
assert_compatible GUT.SMConstantContentRanks.dimension => Physics.SMConstantContentRanks.dimension
assert_compatible GUT.SMConstantContentRanks.evaluate => Physics.SMConstantContentRanks.evaluate
assert_compatible GUT.SMConstantContentRanks.evaluate_sound => Physics.SMConstantContentRanks.evaluate_sound
assert_compatible GUT.SMConstantContentRanks.fieldFinite => Physics.SMConstantContentRanks.fieldFinite
assert_compatible GUT.SMConstantContentRanks.fixed_above => Physics.SMConstantContentRanks.fixed_above
assert_compatible GUT.SMConstantContentRanks.fixed_charged => Physics.SMConstantContentRanks.fixed_charged
assert_compatible GUT.SMConstantContentRanks.fixed_llhh => Physics.SMConstantContentRanks.fixed_llhh
assert_compatible GUT.SMConstantContentRanks.fixed_odd => Physics.SMConstantContentRanks.fixed_odd
assert_compatible GUT.SMConstantContentRanks.pattern => Physics.SMConstantContentRanks.pattern
assert_compatible GUT.SMConstantContentRanks.pattern.eq_1 => Physics.SMConstantContentRanks.pattern.eq_1
assert_compatible GUT.SMConstantContentRanks.source_dimension => Physics.SMConstantContentRanks.source_dimension
assert_compatible GUT.SMContentWeakBound.hypercharge.eq_1 => Physics.SMContentWeakBound.hypercharge.eq_1
