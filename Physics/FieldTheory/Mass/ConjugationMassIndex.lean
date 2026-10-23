import Physics.FieldTheory.Mass.Spectrum.ConjugationMassIndex
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.ConjugationMassIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ConjugationMassIndex.radical_dual_character_invariant => Physics.ConjugationMassIndex.radical_dual_character_invariant,
  GUT.ConjugationMassIndex.radical_dual_character_invariant_prod => Physics.ConjugationMassIndex.radical_dual_character_invariant_prod
]

assert_compatible GUT.ConjugationMassIndex.radical_dual_character_invariant => Physics.ConjugationMassIndex.radical_dual_character_invariant
assert_compatible GUT.ConjugationMassIndex.radical_dual_character_invariant_prod => Physics.ConjugationMassIndex.radical_dual_character_invariant_prod
