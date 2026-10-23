import Physics.StandardModel.Spectrum.Representations.PairwisePositiveSpeciesIndex
import Physics.StandardModel.Spectrum.SharedPositiveSpeciesIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.PairwisePositiveSpeciesIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairwisePositiveSpeciesIndex.PairwisePositive => Physics.PairwisePositiveSpeciesIndex.PairwisePositive,
  GUT.PairwisePositiveSpeciesIndex.of_shared => Physics.PairwisePositiveSpeciesIndex.of_shared,
  GUT.PairwisePositiveSpeciesIndex.pairwise_quotients => Physics.PairwisePositiveSpeciesIndex.pairwise_quotients
]

assert_compatible GUT.PairwisePositiveSpeciesIndex.PairwisePositive => Physics.PairwisePositiveSpeciesIndex.PairwisePositive
assert_compatible GUT.PairwisePositiveSpeciesIndex.of_shared => Physics.PairwisePositiveSpeciesIndex.of_shared
assert_compatible GUT.PairwisePositiveSpeciesIndex.pairwise_quotients => Physics.PairwisePositiveSpeciesIndex.pairwise_quotients
