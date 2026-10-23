import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungData
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungData instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkYoungData.normalization => Physics.LiSixQuarkYoungData.normalization,
  GUT.LiSixQuarkYoungData.permutationData => Physics.LiSixQuarkYoungData.permutationData,
  GUT.LiSixQuarkYoungData.seedColorData => Physics.LiSixQuarkYoungData.seedColorData,
  GUT.LiSixQuarkYoungData.youngWeights => Physics.LiSixQuarkYoungData.youngWeights
]

assert_compatible GUT.LiSixQuarkYoungData.normalization => Physics.LiSixQuarkYoungData.normalization
assert_compatible GUT.LiSixQuarkYoungData.permutationData => Physics.LiSixQuarkYoungData.permutationData
assert_compatible GUT.LiSixQuarkYoungData.seedColorData => Physics.LiSixQuarkYoungData.seedColorData
assert_compatible GUT.LiSixQuarkYoungData.youngWeights => Physics.LiSixQuarkYoungData.youngWeights
