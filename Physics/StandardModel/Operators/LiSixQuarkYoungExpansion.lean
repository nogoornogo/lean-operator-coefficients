import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungExpansion
import Physics.StandardModel.Operators.LiSixQuarkYoungOperators
import Physics.StandardModel.Operators.LiSixQuarkYoungData
import Physics.StandardModel.Operators.SixQuarkSpeciesQuotient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkYoungExpansion instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkYoungData.normalization.eq_1 => Physics.LiSixQuarkYoungData.normalization.eq_1,
  GUT.LiSixQuarkYoungData.permutationData.eq_1 => Physics.LiSixQuarkYoungData.permutationData.eq_1,
  GUT.LiSixQuarkYoungData.youngWeights.eq_1 => Physics.LiSixQuarkYoungData.youngWeights.eq_1,
  GUT.LiSixQuarkYoungExpansion.expanded_eq_factored => Physics.LiSixQuarkYoungExpansion.expanded_eq_factored,
  GUT.LiSixQuarkYoungExpansion.functionAction => Physics.LiSixQuarkYoungExpansion.functionAction,
  GUT.LiSixQuarkYoungExpansion.functionAction.eq_1 => Physics.LiSixQuarkYoungExpansion.functionAction.eq_1,
  GUT.LiSixQuarkYoungExpansion.normalization_eq_primitive => Physics.LiSixQuarkYoungExpansion.normalization_eq_primitive,
  GUT.LiSixQuarkYoungExpansion.normalized_eq_young => Physics.LiSixQuarkYoungExpansion.normalized_eq_young,
  GUT.LiSixQuarkYoungExpansion.paperInverse => Physics.LiSixQuarkYoungExpansion.paperInverse,
  GUT.LiSixQuarkYoungExpansion.paperInverse.eq_1 => Physics.LiSixQuarkYoungExpansion.paperInverse.eq_1,
  GUT.LiSixQuarkYoungExpansion.paperInverse_paperMap => Physics.LiSixQuarkYoungExpansion.paperInverse_paperMap,
  GUT.LiSixQuarkYoungExpansion.paperMap => Physics.LiSixQuarkYoungExpansion.paperMap,
  GUT.LiSixQuarkYoungExpansion.paperMap.eq_1 => Physics.LiSixQuarkYoungExpansion.paperMap.eq_1,
  GUT.LiSixQuarkYoungExpansion.repoMap => Physics.LiSixQuarkYoungExpansion.repoMap,
  GUT.LiSixQuarkYoungExpansion.repoMap.eq_1 => Physics.LiSixQuarkYoungExpansion.repoMap.eq_1,
  GUT.LiSixQuarkYoungExpansion.repoMap_paperMap => Physics.LiSixQuarkYoungExpansion.repoMap_paperMap,
  GUT.LiSixQuarkYoungExpansion.unscaled => Physics.LiSixQuarkYoungExpansion.unscaled,
  GUT.LiSixQuarkYoungExpansion.unscaled.eq_1 => Physics.LiSixQuarkYoungExpansion.unscaled.eq_1,
  GUT.LiSixQuarkYoungExpansion.weighted => Physics.LiSixQuarkYoungExpansion.weighted,
  GUT.LiSixQuarkYoungExpansion.weighted.eq_1 => Physics.LiSixQuarkYoungExpansion.weighted.eq_1
]

assert_compatible GUT.LiSixQuarkYoungData.normalization.eq_1 => Physics.LiSixQuarkYoungData.normalization.eq_1
assert_compatible GUT.LiSixQuarkYoungData.permutationData.eq_1 => Physics.LiSixQuarkYoungData.permutationData.eq_1
assert_compatible GUT.LiSixQuarkYoungData.youngWeights.eq_1 => Physics.LiSixQuarkYoungData.youngWeights.eq_1
assert_compatible GUT.LiSixQuarkYoungExpansion.expanded_eq_factored => Physics.LiSixQuarkYoungExpansion.expanded_eq_factored
assert_compatible GUT.LiSixQuarkYoungExpansion.functionAction => Physics.LiSixQuarkYoungExpansion.functionAction
assert_compatible GUT.LiSixQuarkYoungExpansion.functionAction.eq_1 => Physics.LiSixQuarkYoungExpansion.functionAction.eq_1
assert_compatible GUT.LiSixQuarkYoungExpansion.normalization_eq_primitive => Physics.LiSixQuarkYoungExpansion.normalization_eq_primitive
assert_compatible GUT.LiSixQuarkYoungExpansion.normalized_eq_young => Physics.LiSixQuarkYoungExpansion.normalized_eq_young
assert_compatible GUT.LiSixQuarkYoungExpansion.paperInverse => Physics.LiSixQuarkYoungExpansion.paperInverse
assert_compatible GUT.LiSixQuarkYoungExpansion.paperInverse.eq_1 => Physics.LiSixQuarkYoungExpansion.paperInverse.eq_1
assert_compatible GUT.LiSixQuarkYoungExpansion.paperInverse_paperMap => Physics.LiSixQuarkYoungExpansion.paperInverse_paperMap
assert_compatible GUT.LiSixQuarkYoungExpansion.paperMap => Physics.LiSixQuarkYoungExpansion.paperMap
assert_compatible GUT.LiSixQuarkYoungExpansion.paperMap.eq_1 => Physics.LiSixQuarkYoungExpansion.paperMap.eq_1
assert_compatible GUT.LiSixQuarkYoungExpansion.repoMap => Physics.LiSixQuarkYoungExpansion.repoMap
assert_compatible GUT.LiSixQuarkYoungExpansion.repoMap.eq_1 => Physics.LiSixQuarkYoungExpansion.repoMap.eq_1
assert_compatible GUT.LiSixQuarkYoungExpansion.repoMap_paperMap => Physics.LiSixQuarkYoungExpansion.repoMap_paperMap
assert_compatible GUT.LiSixQuarkYoungExpansion.unscaled => Physics.LiSixQuarkYoungExpansion.unscaled
assert_compatible GUT.LiSixQuarkYoungExpansion.unscaled.eq_1 => Physics.LiSixQuarkYoungExpansion.unscaled.eq_1
assert_compatible GUT.LiSixQuarkYoungExpansion.weighted => Physics.LiSixQuarkYoungExpansion.weighted
assert_compatible GUT.LiSixQuarkYoungExpansion.weighted.eq_1 => Physics.LiSixQuarkYoungExpansion.weighted.eq_1
