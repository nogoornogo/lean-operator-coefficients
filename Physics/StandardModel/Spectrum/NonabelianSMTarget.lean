import Physics.StandardModel.Spectrum.Representations.NonabelianSMTarget
import Physics.FieldTheory.Mass.ResidualMassIndex
import Physics.StandardModel.Spectrum.ConjugationSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.NonabelianSMTarget instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.NonabelianSMTarget.Matches => Physics.NonabelianSMTarget.Matches,
  GUT.NonabelianSMTarget.characters_compatible => Physics.NonabelianSMTarget.characters_compatible,
  GUT.NonabelianSMTarget.index_permute => Physics.NonabelianSMTarget.index_permute,
  GUT.NonabelianSMTarget.species => Physics.NonabelianSMTarget.species,
  GUT.NonabelianSMTarget.target_character_eq => Physics.NonabelianSMTarget.target_character_eq,
  GUT.NonabelianSMTarget.torusPermutation => Physics.NonabelianSMTarget.torusPermutation,
  GUT.NonabelianSMTarget.weightCharacter_comp => Physics.NonabelianSMTarget.weightCharacter_comp
]

assert_compatible GUT.NonabelianSMTarget.Matches => Physics.NonabelianSMTarget.Matches
assert_compatible GUT.NonabelianSMTarget.characters_compatible => Physics.NonabelianSMTarget.characters_compatible
assert_compatible GUT.NonabelianSMTarget.index_permute => Physics.NonabelianSMTarget.index_permute
assert_compatible GUT.NonabelianSMTarget.species => Physics.NonabelianSMTarget.species
assert_compatible GUT.NonabelianSMTarget.target_character_eq => Physics.NonabelianSMTarget.target_character_eq
assert_compatible GUT.NonabelianSMTarget.torusPermutation => Physics.NonabelianSMTarget.torusPermutation
assert_compatible GUT.NonabelianSMTarget.weightCharacter_comp => Physics.NonabelianSMTarget.weightCharacter_comp
