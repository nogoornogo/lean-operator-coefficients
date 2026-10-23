import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkRecipe
import Physics.StandardModel.Operators.LiSixQuarkReducedAction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkRecipe instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkRecipe.extraction_orbit => Physics.HeeckLeSixQuarkRecipe.extraction_orbit,
  GUT.HeeckLeSixQuarkRecipe.extraction_seed => Physics.HeeckLeSixQuarkRecipe.extraction_seed,
  GUT.HeeckLeSixQuarkRecipe.map_color => Physics.HeeckLeSixQuarkRecipe.map_color,
  GUT.HeeckLeSixQuarkRecipe.map_orbit => Physics.HeeckLeSixQuarkRecipe.map_orbit,
  GUT.HeeckLeSixQuarkRecipe.map_seed => Physics.HeeckLeSixQuarkRecipe.map_seed,
  GUT.HeeckLeSixQuarkRecipe.map_spin => Physics.HeeckLeSixQuarkRecipe.map_spin,
  GUT.HeeckLeSixQuarkRecipe.orbit => Physics.HeeckLeSixQuarkRecipe.orbit,
  GUT.HeeckLeSixQuarkRecipe.rawColor => Physics.HeeckLeSixQuarkRecipe.rawColor,
  GUT.HeeckLeSixQuarkRecipe.rawColor.eq_1 => Physics.HeeckLeSixQuarkRecipe.rawColor.eq_1,
  GUT.HeeckLeSixQuarkRecipe.rawColor.eq_2 => Physics.HeeckLeSixQuarkRecipe.rawColor.eq_2,
  GUT.HeeckLeSixQuarkRecipe.rawSpin => Physics.HeeckLeSixQuarkRecipe.rawSpin,
  GUT.HeeckLeSixQuarkRecipe.rawSpin.eq_1 => Physics.HeeckLeSixQuarkRecipe.rawSpin.eq_1,
  GUT.HeeckLeSixQuarkRecipe.reducedOrbit => Physics.HeeckLeSixQuarkRecipe.reducedOrbit,
  GUT.HeeckLeSixQuarkRecipe.reducedSeed => Physics.HeeckLeSixQuarkRecipe.reducedSeed,
  GUT.HeeckLeSixQuarkRecipe.seed => Physics.HeeckLeSixQuarkRecipe.seed,
  GUT.HeeckLeSixQuarkRecipe.selectedSeed => Physics.HeeckLeSixQuarkRecipe.selectedSeed,
  GUT.HeeckLeSixQuarkRecipe.selectedWord => Physics.HeeckLeSixQuarkRecipe.selectedWord
]

assert_compatible GUT.HeeckLeSixQuarkRecipe.extraction_orbit => Physics.HeeckLeSixQuarkRecipe.extraction_orbit
assert_compatible GUT.HeeckLeSixQuarkRecipe.extraction_seed => Physics.HeeckLeSixQuarkRecipe.extraction_seed
assert_compatible GUT.HeeckLeSixQuarkRecipe.map_color => Physics.HeeckLeSixQuarkRecipe.map_color
assert_compatible GUT.HeeckLeSixQuarkRecipe.map_orbit => Physics.HeeckLeSixQuarkRecipe.map_orbit
assert_compatible GUT.HeeckLeSixQuarkRecipe.map_seed => Physics.HeeckLeSixQuarkRecipe.map_seed
assert_compatible GUT.HeeckLeSixQuarkRecipe.map_spin => Physics.HeeckLeSixQuarkRecipe.map_spin
assert_compatible GUT.HeeckLeSixQuarkRecipe.orbit => Physics.HeeckLeSixQuarkRecipe.orbit
assert_compatible GUT.HeeckLeSixQuarkRecipe.rawColor => Physics.HeeckLeSixQuarkRecipe.rawColor
assert_compatible GUT.HeeckLeSixQuarkRecipe.rawColor.eq_1 => Physics.HeeckLeSixQuarkRecipe.rawColor.eq_1
assert_compatible GUT.HeeckLeSixQuarkRecipe.rawColor.eq_2 => Physics.HeeckLeSixQuarkRecipe.rawColor.eq_2
assert_compatible GUT.HeeckLeSixQuarkRecipe.rawSpin => Physics.HeeckLeSixQuarkRecipe.rawSpin
assert_compatible GUT.HeeckLeSixQuarkRecipe.rawSpin.eq_1 => Physics.HeeckLeSixQuarkRecipe.rawSpin.eq_1
assert_compatible GUT.HeeckLeSixQuarkRecipe.reducedOrbit => Physics.HeeckLeSixQuarkRecipe.reducedOrbit
assert_compatible GUT.HeeckLeSixQuarkRecipe.reducedSeed => Physics.HeeckLeSixQuarkRecipe.reducedSeed
assert_compatible GUT.HeeckLeSixQuarkRecipe.seed => Physics.HeeckLeSixQuarkRecipe.seed
assert_compatible GUT.HeeckLeSixQuarkRecipe.selectedSeed => Physics.HeeckLeSixQuarkRecipe.selectedSeed
assert_compatible GUT.HeeckLeSixQuarkRecipe.selectedWord => Physics.HeeckLeSixQuarkRecipe.selectedWord
