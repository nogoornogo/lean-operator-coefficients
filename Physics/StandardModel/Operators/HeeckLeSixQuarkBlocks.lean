import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkBlocks
import Physics.StandardModel.Operators.HeeckLeSixQuarkRecipe
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkBlocks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkBlocks.colorBase => Physics.HeeckLeSixQuarkBlocks.colorBase,
  GUT.HeeckLeSixQuarkBlocks.colorBase.eq_1 => Physics.HeeckLeSixQuarkBlocks.colorBase.eq_1,
  GUT.HeeckLeSixQuarkBlocks.colorBase.eq_2 => Physics.HeeckLeSixQuarkBlocks.colorBase.eq_2,
  GUT.HeeckLeSixQuarkBlocks.color_amplitude => Physics.HeeckLeSixQuarkBlocks.color_amplitude,
  GUT.HeeckLeSixQuarkBlocks.normalize => Physics.HeeckLeSixQuarkBlocks.normalize,
  GUT.HeeckLeSixQuarkBlocks.normalize.eq_1 => Physics.HeeckLeSixQuarkBlocks.normalize.eq_1,
  GUT.HeeckLeSixQuarkBlocks.normalize_action => Physics.HeeckLeSixQuarkBlocks.normalize_action,
  GUT.HeeckLeSixQuarkBlocks.normalize_orbit => Physics.HeeckLeSixQuarkBlocks.normalize_orbit,
  GUT.HeeckLeSixQuarkBlocks.normalize_seed => Physics.HeeckLeSixQuarkBlocks.normalize_seed,
  GUT.HeeckLeSixQuarkBlocks.normalize_word => Physics.HeeckLeSixQuarkBlocks.normalize_word,
  GUT.HeeckLeSixQuarkBlocks.orbit => Physics.HeeckLeSixQuarkBlocks.orbit,
  GUT.HeeckLeSixQuarkBlocks.scaleLinear => Physics.HeeckLeSixQuarkBlocks.scaleLinear,
  GUT.HeeckLeSixQuarkBlocks.scaleLinear.eq_1 => Physics.HeeckLeSixQuarkBlocks.scaleLinear.eq_1,
  GUT.HeeckLeSixQuarkBlocks.scaleSpin => Physics.HeeckLeSixQuarkBlocks.scaleSpin,
  GUT.HeeckLeSixQuarkBlocks.scaleSpin.eq_1 => Physics.HeeckLeSixQuarkBlocks.scaleSpin.eq_1,
  GUT.HeeckLeSixQuarkBlocks.source => Physics.HeeckLeSixQuarkBlocks.source,
  GUT.HeeckLeSixQuarkBlocks.source.eq_1 => Physics.HeeckLeSixQuarkBlocks.source.eq_1,
  GUT.HeeckLeSixQuarkBlocks.source0_pair_zero => Physics.HeeckLeSixQuarkBlocks.source0_pair_zero,
  GUT.HeeckLeSixQuarkBlocks.spinBase => Physics.HeeckLeSixQuarkBlocks.spinBase,
  GUT.HeeckLeSixQuarkBlocks.spinBase.eq_1 => Physics.HeeckLeSixQuarkBlocks.spinBase.eq_1,
  GUT.HeeckLeSixQuarkBlocks.spin_amplitude => Physics.HeeckLeSixQuarkBlocks.spin_amplitude,
  GUT.HeeckLeSixQuarkBlocks.spin_scale_commute => Physics.HeeckLeSixQuarkBlocks.spin_scale_commute,
  GUT.HeeckLeSixQuarkBlocks.unscale => Physics.HeeckLeSixQuarkBlocks.unscale,
  GUT.HeeckLeSixQuarkBlocks.unscale.eq_1 => Physics.HeeckLeSixQuarkBlocks.unscale.eq_1,
  GUT.HeeckLeSixQuarkBlocks.unscale_normalize => Physics.HeeckLeSixQuarkBlocks.unscale_normalize
]

assert_compatible GUT.HeeckLeSixQuarkBlocks.colorBase => Physics.HeeckLeSixQuarkBlocks.colorBase
assert_compatible GUT.HeeckLeSixQuarkBlocks.colorBase.eq_1 => Physics.HeeckLeSixQuarkBlocks.colorBase.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.colorBase.eq_2 => Physics.HeeckLeSixQuarkBlocks.colorBase.eq_2
assert_compatible GUT.HeeckLeSixQuarkBlocks.color_amplitude => Physics.HeeckLeSixQuarkBlocks.color_amplitude
assert_compatible GUT.HeeckLeSixQuarkBlocks.normalize => Physics.HeeckLeSixQuarkBlocks.normalize
assert_compatible GUT.HeeckLeSixQuarkBlocks.normalize.eq_1 => Physics.HeeckLeSixQuarkBlocks.normalize.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.normalize_action => Physics.HeeckLeSixQuarkBlocks.normalize_action
assert_compatible GUT.HeeckLeSixQuarkBlocks.normalize_orbit => Physics.HeeckLeSixQuarkBlocks.normalize_orbit
assert_compatible GUT.HeeckLeSixQuarkBlocks.normalize_seed => Physics.HeeckLeSixQuarkBlocks.normalize_seed
assert_compatible GUT.HeeckLeSixQuarkBlocks.normalize_word => Physics.HeeckLeSixQuarkBlocks.normalize_word
assert_compatible GUT.HeeckLeSixQuarkBlocks.orbit => Physics.HeeckLeSixQuarkBlocks.orbit
assert_compatible GUT.HeeckLeSixQuarkBlocks.scaleLinear => Physics.HeeckLeSixQuarkBlocks.scaleLinear
assert_compatible GUT.HeeckLeSixQuarkBlocks.scaleLinear.eq_1 => Physics.HeeckLeSixQuarkBlocks.scaleLinear.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.scaleSpin => Physics.HeeckLeSixQuarkBlocks.scaleSpin
assert_compatible GUT.HeeckLeSixQuarkBlocks.scaleSpin.eq_1 => Physics.HeeckLeSixQuarkBlocks.scaleSpin.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.source => Physics.HeeckLeSixQuarkBlocks.source
assert_compatible GUT.HeeckLeSixQuarkBlocks.source.eq_1 => Physics.HeeckLeSixQuarkBlocks.source.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.source0_pair_zero => Physics.HeeckLeSixQuarkBlocks.source0_pair_zero
assert_compatible GUT.HeeckLeSixQuarkBlocks.spinBase => Physics.HeeckLeSixQuarkBlocks.spinBase
assert_compatible GUT.HeeckLeSixQuarkBlocks.spinBase.eq_1 => Physics.HeeckLeSixQuarkBlocks.spinBase.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.spin_amplitude => Physics.HeeckLeSixQuarkBlocks.spin_amplitude
assert_compatible GUT.HeeckLeSixQuarkBlocks.spin_scale_commute => Physics.HeeckLeSixQuarkBlocks.spin_scale_commute
assert_compatible GUT.HeeckLeSixQuarkBlocks.unscale => Physics.HeeckLeSixQuarkBlocks.unscale
assert_compatible GUT.HeeckLeSixQuarkBlocks.unscale.eq_1 => Physics.HeeckLeSixQuarkBlocks.unscale.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.unscale_normalize => Physics.HeeckLeSixQuarkBlocks.unscale_normalize
