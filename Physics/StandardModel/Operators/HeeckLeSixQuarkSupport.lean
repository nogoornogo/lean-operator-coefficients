import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkSupport
import Physics.StandardModel.Operators.HeeckLeSixQuarkBlocks
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkSupport.PairZero => Physics.HeeckLeSixQuarkSupport.PairZero,
  GUT.HeeckLeSixQuarkSupport.action_pair_zero => Physics.HeeckLeSixQuarkSupport.action_pair_zero,
  GUT.HeeckLeSixQuarkSupport.color_pair_zero => Physics.HeeckLeSixQuarkSupport.color_pair_zero,
  GUT.HeeckLeSixQuarkSupport.orbit_source0_pair_zero => Physics.HeeckLeSixQuarkSupport.orbit_source0_pair_zero,
  GUT.HeeckLeSixQuarkSupport.source0_pair_zero => Physics.HeeckLeSixQuarkSupport.source0_pair_zero,
  GUT.HeeckLeSixQuarkSupport.word_pair_zero => Physics.HeeckLeSixQuarkSupport.word_pair_zero
]

assert_compatible GUT.HeeckLeSixQuarkSupport.PairZero => Physics.HeeckLeSixQuarkSupport.PairZero
assert_compatible GUT.HeeckLeSixQuarkSupport.action_pair_zero => Physics.HeeckLeSixQuarkSupport.action_pair_zero
assert_compatible GUT.HeeckLeSixQuarkSupport.color_pair_zero => Physics.HeeckLeSixQuarkSupport.color_pair_zero
assert_compatible GUT.HeeckLeSixQuarkSupport.orbit_source0_pair_zero => Physics.HeeckLeSixQuarkSupport.orbit_source0_pair_zero
assert_compatible GUT.HeeckLeSixQuarkSupport.source0_pair_zero => Physics.HeeckLeSixQuarkSupport.source0_pair_zero
assert_compatible GUT.HeeckLeSixQuarkSupport.word_pair_zero => Physics.HeeckLeSixQuarkSupport.word_pair_zero
