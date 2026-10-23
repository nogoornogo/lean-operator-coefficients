import Physics.StandardModel.Operators.Selection.FlavoredCyclicControls
import Physics.StandardModel.Operators.FlavoredCyclicSelection
import Physics.StandardModel.Operators.CyclicResidualSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.FlavoredCyclicControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.CyclicResidualSelection.quarkParity.eq_1 => Physics.CyclicResidualSelection.quarkParity.eq_1,
  GUT.FlavoredCyclicControls.empty_total => Physics.FlavoredCyclicControls.empty_total,
  GUT.FlavoredCyclicControls.empty_weinberg => Physics.FlavoredCyclicControls.empty_weinberg,
  GUT.FlavoredCyclicControls.isEmpty_constant => Physics.FlavoredCyclicControls.isEmpty_constant,
  GUT.FlavoredCyclicControls.nonuniform => Physics.FlavoredCyclicControls.nonuniform,
  GUT.FlavoredCyclicControls.nonuniform_ordered_count => Physics.FlavoredCyclicControls.nonuniform_ordered_count,
  GUT.FlavoredCyclicControls.nonuniform_qqql => Physics.FlavoredCyclicControls.nonuniform_qqql,
  GUT.FlavoredCyclicControls.quarkParity => Physics.FlavoredCyclicControls.quarkParity,
  GUT.FlavoredCyclicControls.quarkParity.eq_1 => Physics.FlavoredCyclicControls.quarkParity.eq_1,
  GUT.FlavoredCyclicControls.singleton_forbidden_iff => Physics.FlavoredCyclicControls.singleton_forbidden_iff,
  GUT.FlavoredCyclicControls.singleton_quarkParity_forbidden => Physics.FlavoredCyclicControls.singleton_quarkParity_forbidden,
  GUT.FlavoredCyclicControls.singleton_quarkParity_weinberg => Physics.FlavoredCyclicControls.singleton_quarkParity_weinberg,
  GUT.FlavoredCyclicControls.singleton_weinberg_iff => Physics.FlavoredCyclicControls.singleton_weinberg_iff,
  GUT.FlavoredCyclicControls.symmetric_constant => Physics.FlavoredCyclicControls.symmetric_constant,
  GUT.FlavoredCyclicControls.trivial_three_generation => Physics.FlavoredCyclicControls.trivial_three_generation,
  GUT.FlavoredCyclicControls.unequalIndex => Physics.FlavoredCyclicControls.unequalIndex,
  GUT.FlavoredCyclicControls.unequal_species_total => Physics.FlavoredCyclicControls.unequal_species_total
]

assert_compatible GUT.CyclicResidualSelection.quarkParity.eq_1 => Physics.CyclicResidualSelection.quarkParity.eq_1
assert_compatible GUT.FlavoredCyclicControls.empty_total => Physics.FlavoredCyclicControls.empty_total
assert_compatible GUT.FlavoredCyclicControls.empty_weinberg => Physics.FlavoredCyclicControls.empty_weinberg
assert_compatible GUT.FlavoredCyclicControls.isEmpty_constant => Physics.FlavoredCyclicControls.isEmpty_constant
assert_compatible GUT.FlavoredCyclicControls.nonuniform => Physics.FlavoredCyclicControls.nonuniform
assert_compatible GUT.FlavoredCyclicControls.nonuniform_ordered_count => Physics.FlavoredCyclicControls.nonuniform_ordered_count
assert_compatible GUT.FlavoredCyclicControls.nonuniform_qqql => Physics.FlavoredCyclicControls.nonuniform_qqql
assert_compatible GUT.FlavoredCyclicControls.quarkParity => Physics.FlavoredCyclicControls.quarkParity
assert_compatible GUT.FlavoredCyclicControls.quarkParity.eq_1 => Physics.FlavoredCyclicControls.quarkParity.eq_1
assert_compatible GUT.FlavoredCyclicControls.singleton_forbidden_iff => Physics.FlavoredCyclicControls.singleton_forbidden_iff
assert_compatible GUT.FlavoredCyclicControls.singleton_quarkParity_forbidden => Physics.FlavoredCyclicControls.singleton_quarkParity_forbidden
assert_compatible GUT.FlavoredCyclicControls.singleton_quarkParity_weinberg => Physics.FlavoredCyclicControls.singleton_quarkParity_weinberg
assert_compatible GUT.FlavoredCyclicControls.singleton_weinberg_iff => Physics.FlavoredCyclicControls.singleton_weinberg_iff
assert_compatible GUT.FlavoredCyclicControls.symmetric_constant => Physics.FlavoredCyclicControls.symmetric_constant
assert_compatible GUT.FlavoredCyclicControls.trivial_three_generation => Physics.FlavoredCyclicControls.trivial_three_generation
assert_compatible GUT.FlavoredCyclicControls.unequalIndex => Physics.FlavoredCyclicControls.unequalIndex
assert_compatible GUT.FlavoredCyclicControls.unequal_species_total => Physics.FlavoredCyclicControls.unequal_species_total
