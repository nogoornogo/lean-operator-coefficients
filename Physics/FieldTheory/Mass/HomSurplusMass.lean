import Physics.FieldTheory.Mass.Surplus.HomSurplusMass
import Physics.FieldTheory.Mass.BipartiteNormalForm
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.HomSurplusMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HomSurplusMass.arbitrary_mass_survival => Physics.HomSurplusMass.arbitrary_mass_survival,
  GUT.HomSurplusMass.noPairings_finrank_zero => Physics.HomSurplusMass.noPairings_finrank_zero,
  GUT.HomSurplusMass.no_light_species_necessary => Physics.HomSurplusMass.no_light_species_necessary,
  GUT.HomSurplusMass.radical_hom_zero => Physics.HomSurplusMass.radical_hom_zero,
  GUT.HomSurplusMass.radical_multiplicity_bound => Physics.HomSurplusMass.radical_multiplicity_bound,
  GUT.HomSurplusMass.source_multiplicity => Physics.HomSurplusMass.source_multiplicity,
  GUT.HomSurplusMass.target_multiplicity => Physics.HomSurplusMass.target_multiplicity
]

assert_compatible GUT.HomSurplusMass.arbitrary_mass_survival => Physics.HomSurplusMass.arbitrary_mass_survival
assert_compatible GUT.HomSurplusMass.noPairings_finrank_zero => Physics.HomSurplusMass.noPairings_finrank_zero
assert_compatible GUT.HomSurplusMass.no_light_species_necessary => Physics.HomSurplusMass.no_light_species_necessary
assert_compatible GUT.HomSurplusMass.radical_hom_zero => Physics.HomSurplusMass.radical_hom_zero
assert_compatible GUT.HomSurplusMass.radical_multiplicity_bound => Physics.HomSurplusMass.radical_multiplicity_bound
assert_compatible GUT.HomSurplusMass.source_multiplicity => Physics.HomSurplusMass.source_multiplicity
assert_compatible GUT.HomSurplusMass.target_multiplicity => Physics.HomSurplusMass.target_multiplicity
