import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFiniteData
import Physics.StandardModel.Operators.LiSixQuarkOrbitRecipe
import Physics.StandardModel.Operators.LiSixQuarkYoungData
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFiniteData instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkConvention.basisEntry => Physics.LiSixQuarkConvention.basisEntry,
  GUT.LiSixQuarkConvention.colorEpsilon => Physics.LiSixQuarkConvention.colorEpsilon,
  GUT.LiSixQuarkConvention.normalization => Physics.LiSixQuarkConvention.normalization,
  GUT.LiSixQuarkConvention.permutationData => Physics.LiSixQuarkConvention.permutationData,
  GUT.LiSixQuarkConvention.rationalSeedCoordinates => Physics.LiSixQuarkConvention.rationalSeedCoordinates,
  GUT.LiSixQuarkConvention.rationalValue => Physics.LiSixQuarkConvention.rationalValue,
  GUT.LiSixQuarkConvention.seedColorData => Physics.LiSixQuarkConvention.seedColorData,
  GUT.LiSixQuarkConvention.seedCoordinates => Physics.LiSixQuarkConvention.seedCoordinates,
  GUT.LiSixQuarkConvention.spinEpsilon => Physics.LiSixQuarkConvention.spinEpsilon,
  GUT.LiSixQuarkConvention.youngWeights => Physics.LiSixQuarkConvention.youngWeights
]

assert_compatible GUT.LiSixQuarkConvention.basisEntry => Physics.LiSixQuarkConvention.basisEntry
assert_compatible GUT.LiSixQuarkConvention.colorEpsilon => Physics.LiSixQuarkConvention.colorEpsilon
assert_compatible GUT.LiSixQuarkConvention.normalization => Physics.LiSixQuarkConvention.normalization
assert_compatible GUT.LiSixQuarkConvention.permutationData => Physics.LiSixQuarkConvention.permutationData
assert_compatible GUT.LiSixQuarkConvention.rationalSeedCoordinates => Physics.LiSixQuarkConvention.rationalSeedCoordinates
assert_compatible GUT.LiSixQuarkConvention.rationalValue => Physics.LiSixQuarkConvention.rationalValue
assert_compatible GUT.LiSixQuarkConvention.seedColorData => Physics.LiSixQuarkConvention.seedColorData
assert_compatible GUT.LiSixQuarkConvention.seedCoordinates => Physics.LiSixQuarkConvention.seedCoordinates
assert_compatible GUT.LiSixQuarkConvention.spinEpsilon => Physics.LiSixQuarkConvention.spinEpsilon
assert_compatible GUT.LiSixQuarkConvention.youngWeights => Physics.LiSixQuarkConvention.youngWeights
