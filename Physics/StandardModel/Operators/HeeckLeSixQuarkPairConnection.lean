import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairConnection
import Physics.StandardModel.Operators.HeeckLeSixQuarkPairCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairConnection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkAssemblyBase.even.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.even.eq_1,
  GUT.HeeckLeSixQuarkAssemblyBase.odd.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.odd.eq_1,
  GUT.HeeckLeSixQuarkBlocks.orbit.eq_1 => Physics.HeeckLeSixQuarkBlocks.orbit.eq_1,
  GUT.HeeckLeSixQuarkPairConnection.even_even => Physics.HeeckLeSixQuarkPairConnection.even_even,
  GUT.HeeckLeSixQuarkPairConnection.even_odd => Physics.HeeckLeSixQuarkPairConnection.even_odd,
  GUT.HeeckLeSixQuarkPairConnection.odd_even => Physics.HeeckLeSixQuarkPairConnection.odd_even,
  GUT.HeeckLeSixQuarkPairConnection.odd_odd => Physics.HeeckLeSixQuarkPairConnection.odd_odd,
  GUT.HeeckLeSixQuarkPairConnection.residual_apply => Physics.HeeckLeSixQuarkPairConnection.residual_apply,
  GUT.HeeckLeSixQuarkPairConnection.residual_even => Physics.HeeckLeSixQuarkPairConnection.residual_even,
  GUT.HeeckLeSixQuarkPairConnection.residual_odd => Physics.HeeckLeSixQuarkPairConnection.residual_odd,
  GUT.HeeckLeSixQuarkRecipe.selectedSeed.eq_1 => Physics.HeeckLeSixQuarkRecipe.selectedSeed.eq_1,
  GUT.HeeckLeSixQuarkRecipe.selectedWord.eq_1 => Physics.HeeckLeSixQuarkRecipe.selectedWord.eq_1
]

assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.even.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.even.eq_1
assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.odd.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.odd.eq_1
assert_compatible GUT.HeeckLeSixQuarkBlocks.orbit.eq_1 => Physics.HeeckLeSixQuarkBlocks.orbit.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairConnection.even_even => Physics.HeeckLeSixQuarkPairConnection.even_even
assert_compatible GUT.HeeckLeSixQuarkPairConnection.even_odd => Physics.HeeckLeSixQuarkPairConnection.even_odd
assert_compatible GUT.HeeckLeSixQuarkPairConnection.odd_even => Physics.HeeckLeSixQuarkPairConnection.odd_even
assert_compatible GUT.HeeckLeSixQuarkPairConnection.odd_odd => Physics.HeeckLeSixQuarkPairConnection.odd_odd
assert_compatible GUT.HeeckLeSixQuarkPairConnection.residual_apply => Physics.HeeckLeSixQuarkPairConnection.residual_apply
assert_compatible GUT.HeeckLeSixQuarkPairConnection.residual_even => Physics.HeeckLeSixQuarkPairConnection.residual_even
assert_compatible GUT.HeeckLeSixQuarkPairConnection.residual_odd => Physics.HeeckLeSixQuarkPairConnection.residual_odd
assert_compatible GUT.HeeckLeSixQuarkRecipe.selectedSeed.eq_1 => Physics.HeeckLeSixQuarkRecipe.selectedSeed.eq_1
assert_compatible GUT.HeeckLeSixQuarkRecipe.selectedWord.eq_1 => Physics.HeeckLeSixQuarkRecipe.selectedWord.eq_1
