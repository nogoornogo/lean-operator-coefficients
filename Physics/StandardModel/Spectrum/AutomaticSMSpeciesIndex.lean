import Physics.StandardModel.Spectrum.Representations.AutomaticSMSpeciesIndex
import Physics.StandardModel.Spectrum.ExactSMResidualSpectrum
import Physics.StandardModel.Spectrum.PairwisePositiveSpeciesIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.AutomaticSMSpeciesIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AutomaticSMSpeciesIndex.Carrier => Physics.AutomaticSMSpeciesIndex.Carrier,
  GUT.AutomaticSMSpeciesIndex.Index => Physics.AutomaticSMSpeciesIndex.Index,
  GUT.AutomaticSMSpeciesIndex.PairwisePositive => Physics.AutomaticSMSpeciesIndex.PairwisePositive,
  GUT.AutomaticSMSpeciesIndex.action => Physics.AutomaticSMSpeciesIndex.action,
  GUT.AutomaticSMSpeciesIndex.coefficients => Physics.AutomaticSMSpeciesIndex.coefficients,
  GUT.AutomaticSMSpeciesIndex.continuous => Physics.AutomaticSMSpeciesIndex.continuous,
  GUT.AutomaticSMSpeciesIndex.index_character => Physics.AutomaticSMSpeciesIndex.index_character,
  GUT.AutomaticSMSpeciesIndex.inequivalent => Physics.AutomaticSMSpeciesIndex.inequivalent,
  GUT.AutomaticSMSpeciesIndex.presentation => Physics.AutomaticSMSpeciesIndex.presentation,
  GUT.AutomaticSMSpeciesIndex.species_matches => Physics.AutomaticSMSpeciesIndex.species_matches
]

assert_compatible GUT.AutomaticSMSpeciesIndex.Carrier => Physics.AutomaticSMSpeciesIndex.Carrier
assert_compatible GUT.AutomaticSMSpeciesIndex.Index => Physics.AutomaticSMSpeciesIndex.Index
assert_compatible GUT.AutomaticSMSpeciesIndex.PairwisePositive => Physics.AutomaticSMSpeciesIndex.PairwisePositive
assert_compatible GUT.AutomaticSMSpeciesIndex.action => Physics.AutomaticSMSpeciesIndex.action
assert_compatible GUT.AutomaticSMSpeciesIndex.coefficients => Physics.AutomaticSMSpeciesIndex.coefficients
assert_compatible GUT.AutomaticSMSpeciesIndex.continuous => Physics.AutomaticSMSpeciesIndex.continuous
assert_compatible GUT.AutomaticSMSpeciesIndex.index_character => Physics.AutomaticSMSpeciesIndex.index_character
assert_compatible GUT.AutomaticSMSpeciesIndex.inequivalent => Physics.AutomaticSMSpeciesIndex.inequivalent
assert_compatible GUT.AutomaticSMSpeciesIndex.presentation => Physics.AutomaticSMSpeciesIndex.presentation
assert_compatible GUT.AutomaticSMSpeciesIndex.species_matches => Physics.AutomaticSMSpeciesIndex.species_matches
