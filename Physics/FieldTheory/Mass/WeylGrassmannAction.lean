import Physics.FieldTheory.Mass.Algebra.WeylGrassmannAction
import Physics.FieldTheory.Spinor.RightWeylChargeConjugation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.WeylGrassmannAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylGrassmannAction.Algebra => Physics.WeylGrassmannAction.Algebra,
  GUT.WeylGrassmannAction.Coordinates => Physics.WeylGrassmannAction.Coordinates,
  GUT.WeylGrassmannAction.action => Physics.WeylGrassmannAction.action,
  GUT.WeylGrassmannAction.action.eq_1 => Physics.WeylGrassmannAction.action.eq_1,
  GUT.WeylGrassmannAction.fourPair => Physics.WeylGrassmannAction.fourPair,
  GUT.WeylGrassmannAction.fourPair.eq_1 => Physics.WeylGrassmannAction.fourPair.eq_1,
  GUT.WeylGrassmannAction.four_component_right => Physics.WeylGrassmannAction.four_component_right,
  GUT.WeylGrassmannAction.generator => Physics.WeylGrassmannAction.generator,
  GUT.WeylGrassmannAction.generator_swap => Physics.WeylGrassmannAction.generator_swap,
  GUT.WeylGrassmannAction.pair => Physics.WeylGrassmannAction.pair,
  GUT.WeylGrassmannAction.pair.eq_1 => Physics.WeylGrassmannAction.pair.eq_1,
  GUT.WeylGrassmannAction.pair_symmetric => Physics.WeylGrassmannAction.pair_symmetric,
  GUT.WeylGrassmannAction.rightComponents => Physics.WeylGrassmannAction.rightComponents,
  GUT.WeylGrassmannAction.rightComponents.eq_1 => Physics.WeylGrassmannAction.rightComponents.eq_1,
  GUT.WeylGrassmannAction.three_species_action => Physics.WeylGrassmannAction.three_species_action
]

assert_compatible GUT.WeylGrassmannAction.Algebra => Physics.WeylGrassmannAction.Algebra
assert_compatible GUT.WeylGrassmannAction.Coordinates => Physics.WeylGrassmannAction.Coordinates
assert_compatible GUT.WeylGrassmannAction.action => Physics.WeylGrassmannAction.action
assert_compatible GUT.WeylGrassmannAction.action.eq_1 => Physics.WeylGrassmannAction.action.eq_1
assert_compatible GUT.WeylGrassmannAction.fourPair => Physics.WeylGrassmannAction.fourPair
assert_compatible GUT.WeylGrassmannAction.fourPair.eq_1 => Physics.WeylGrassmannAction.fourPair.eq_1
assert_compatible GUT.WeylGrassmannAction.four_component_right => Physics.WeylGrassmannAction.four_component_right
assert_compatible GUT.WeylGrassmannAction.generator => Physics.WeylGrassmannAction.generator
assert_compatible GUT.WeylGrassmannAction.generator_swap => Physics.WeylGrassmannAction.generator_swap
assert_compatible GUT.WeylGrassmannAction.pair => Physics.WeylGrassmannAction.pair
assert_compatible GUT.WeylGrassmannAction.pair.eq_1 => Physics.WeylGrassmannAction.pair.eq_1
assert_compatible GUT.WeylGrassmannAction.pair_symmetric => Physics.WeylGrassmannAction.pair_symmetric
assert_compatible GUT.WeylGrassmannAction.rightComponents => Physics.WeylGrassmannAction.rightComponents
assert_compatible GUT.WeylGrassmannAction.rightComponents.eq_1 => Physics.WeylGrassmannAction.rightComponents.eq_1
assert_compatible GUT.WeylGrassmannAction.three_species_action => Physics.WeylGrassmannAction.three_species_action
