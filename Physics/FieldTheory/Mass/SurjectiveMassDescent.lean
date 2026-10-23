import Physics.FieldTheory.Mass.Surplus.SurjectiveMassDescent
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Surplus.SurjectiveMassDescent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InvariantWeylMass.SymmetricMass.descend => Physics.InvariantWeylMass.SymmetricMass.descend,
  GUT.InvariantWeylMass.SymmetricMass.descend_form => Physics.InvariantWeylMass.SymmetricMass.descend_form,
  GUT.InvariantWeylMass.SymmetricMass.descend_radical => Physics.InvariantWeylMass.SymmetricMass.descend_radical,
  GUT.InvariantWeylMass.SymmetricMass.descend_radical_character => Physics.InvariantWeylMass.SymmetricMass.descend_radical_character,
  GUT.InvariantWeylMass.SymmetricMass.descend_radical_comp => Physics.InvariantWeylMass.SymmetricMass.descend_radical_comp
]

assert_compatible GUT.InvariantWeylMass.SymmetricMass.descend => Physics.InvariantWeylMass.SymmetricMass.descend
assert_compatible GUT.InvariantWeylMass.SymmetricMass.descend_form => Physics.InvariantWeylMass.SymmetricMass.descend_form
assert_compatible GUT.InvariantWeylMass.SymmetricMass.descend_radical => Physics.InvariantWeylMass.SymmetricMass.descend_radical
assert_compatible GUT.InvariantWeylMass.SymmetricMass.descend_radical_character => Physics.InvariantWeylMass.SymmetricMass.descend_radical_character
assert_compatible GUT.InvariantWeylMass.SymmetricMass.descend_radical_comp => Physics.InvariantWeylMass.SymmetricMass.descend_radical_comp
