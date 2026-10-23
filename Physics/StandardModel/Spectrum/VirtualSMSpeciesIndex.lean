import Physics.StandardModel.Spectrum.Representations.VirtualSMSpeciesIndex
import Physics.StandardModel.Spectrum.LightSMSpeciesIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.VirtualSMSpeciesIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.VirtualSMSpeciesIndex.SpeciesMatches => Physics.VirtualSMSpeciesIndex.SpeciesMatches,
  GUT.VirtualSMSpeciesIndex.WeightMatches => Physics.VirtualSMSpeciesIndex.WeightMatches,
  GUT.VirtualSMSpeciesIndex.characters_compatible => Physics.VirtualSMSpeciesIndex.characters_compatible,
  GUT.VirtualSMSpeciesIndex.common_quotient => Physics.VirtualSMSpeciesIndex.common_quotient
]

assert_compatible GUT.VirtualSMSpeciesIndex.SpeciesMatches => Physics.VirtualSMSpeciesIndex.SpeciesMatches
assert_compatible GUT.VirtualSMSpeciesIndex.WeightMatches => Physics.VirtualSMSpeciesIndex.WeightMatches
assert_compatible GUT.VirtualSMSpeciesIndex.characters_compatible => Physics.VirtualSMSpeciesIndex.characters_compatible
assert_compatible GUT.VirtualSMSpeciesIndex.common_quotient => Physics.VirtualSMSpeciesIndex.common_quotient
