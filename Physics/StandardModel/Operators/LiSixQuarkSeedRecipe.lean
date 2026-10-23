import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSeedRecipe
import Physics.StandardModel.Operators.LiSixQuarkSemanticSeeds
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSeedRecipe instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkSeedRecipe.complex_projected => Physics.LiSixQuarkSeedRecipe.complex_projected,
  GUT.LiSixQuarkSeedRecipe.complex_raw => Physics.LiSixQuarkSeedRecipe.complex_raw,
  GUT.LiSixQuarkSeedRecipe.mapArray => Physics.LiSixQuarkSeedRecipe.mapArray,
  GUT.LiSixQuarkSeedRecipe.map_action => Physics.LiSixQuarkSeedRecipe.map_action,
  GUT.LiSixQuarkSeedRecipe.map_color => Physics.LiSixQuarkSeedRecipe.map_color,
  GUT.LiSixQuarkSeedRecipe.map_projected => Physics.LiSixQuarkSeedRecipe.map_projected,
  GUT.LiSixQuarkSeedRecipe.map_raw => Physics.LiSixQuarkSeedRecipe.map_raw,
  GUT.LiSixQuarkSeedRecipe.map_spin => Physics.LiSixQuarkSeedRecipe.map_spin,
  GUT.LiSixQuarkSeedRecipe.map_word => Physics.LiSixQuarkSeedRecipe.map_word,
  GUT.LiSixQuarkSeedRecipe.projected => Physics.LiSixQuarkSeedRecipe.projected,
  GUT.LiSixQuarkSeedRecipe.rational_cast => Physics.LiSixQuarkSeedRecipe.rational_cast,
  GUT.LiSixQuarkSeedRecipe.raw => Physics.LiSixQuarkSeedRecipe.raw,
  GUT.LiSixQuarkSeedRecipe.rawColor => Physics.LiSixQuarkSeedRecipe.rawColor,
  GUT.LiSixQuarkSeedRecipe.rawColor.eq_1 => Physics.LiSixQuarkSeedRecipe.rawColor.eq_1,
  GUT.LiSixQuarkSeedRecipe.rawSpin => Physics.LiSixQuarkSeedRecipe.rawSpin,
  GUT.LiSixQuarkSeedRecipe.rawSpin.eq_1 => Physics.LiSixQuarkSeedRecipe.rawSpin.eq_1
]

assert_compatible GUT.LiSixQuarkSeedRecipe.complex_projected => Physics.LiSixQuarkSeedRecipe.complex_projected
assert_compatible GUT.LiSixQuarkSeedRecipe.complex_raw => Physics.LiSixQuarkSeedRecipe.complex_raw
assert_compatible GUT.LiSixQuarkSeedRecipe.mapArray => Physics.LiSixQuarkSeedRecipe.mapArray
assert_compatible GUT.LiSixQuarkSeedRecipe.map_action => Physics.LiSixQuarkSeedRecipe.map_action
assert_compatible GUT.LiSixQuarkSeedRecipe.map_color => Physics.LiSixQuarkSeedRecipe.map_color
assert_compatible GUT.LiSixQuarkSeedRecipe.map_projected => Physics.LiSixQuarkSeedRecipe.map_projected
assert_compatible GUT.LiSixQuarkSeedRecipe.map_raw => Physics.LiSixQuarkSeedRecipe.map_raw
assert_compatible GUT.LiSixQuarkSeedRecipe.map_spin => Physics.LiSixQuarkSeedRecipe.map_spin
assert_compatible GUT.LiSixQuarkSeedRecipe.map_word => Physics.LiSixQuarkSeedRecipe.map_word
assert_compatible GUT.LiSixQuarkSeedRecipe.projected => Physics.LiSixQuarkSeedRecipe.projected
assert_compatible GUT.LiSixQuarkSeedRecipe.rational_cast => Physics.LiSixQuarkSeedRecipe.rational_cast
assert_compatible GUT.LiSixQuarkSeedRecipe.raw => Physics.LiSixQuarkSeedRecipe.raw
assert_compatible GUT.LiSixQuarkSeedRecipe.rawColor => Physics.LiSixQuarkSeedRecipe.rawColor
assert_compatible GUT.LiSixQuarkSeedRecipe.rawColor.eq_1 => Physics.LiSixQuarkSeedRecipe.rawColor.eq_1
assert_compatible GUT.LiSixQuarkSeedRecipe.rawSpin => Physics.LiSixQuarkSeedRecipe.rawSpin
assert_compatible GUT.LiSixQuarkSeedRecipe.rawSpin.eq_1 => Physics.LiSixQuarkSeedRecipe.rawSpin.eq_1
