import Physics.StandardModel.Spectrum.Representations.SharedPositiveSpeciesIndex
import Physics.StandardModel.Spectrum.VirtualSMSpeciesIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.SharedPositiveSpeciesIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SharedPositiveSpeciesIndex.SharedPositive => Physics.SharedPositiveSpeciesIndex.SharedPositive,
  GUT.SharedPositiveSpeciesIndex.common_quotient => Physics.SharedPositiveSpeciesIndex.common_quotient,
  GUT.SharedPositiveSpeciesIndex.of_common_index => Physics.SharedPositiveSpeciesIndex.of_common_index,
  GUT.SharedPositiveSpeciesIndex.of_conjugations => Physics.SharedPositiveSpeciesIndex.of_conjugations
]

assert_compatible GUT.SharedPositiveSpeciesIndex.SharedPositive => Physics.SharedPositiveSpeciesIndex.SharedPositive
assert_compatible GUT.SharedPositiveSpeciesIndex.common_quotient => Physics.SharedPositiveSpeciesIndex.common_quotient
assert_compatible GUT.SharedPositiveSpeciesIndex.of_common_index => Physics.SharedPositiveSpeciesIndex.of_common_index
assert_compatible GUT.SharedPositiveSpeciesIndex.of_conjugations => Physics.SharedPositiveSpeciesIndex.of_conjugations
