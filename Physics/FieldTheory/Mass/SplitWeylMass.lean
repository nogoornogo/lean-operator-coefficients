import Physics.FieldTheory.Mass.Algebra.SplitWeylMass
import Physics.FieldTheory.Mass.InvariantWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.SplitWeylMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SplitWeylMass.Fields => Physics.SplitWeylMass.Fields,
  GUT.SplitWeylMass.mass => Physics.SplitWeylMass.mass,
  GUT.SplitWeylMass.mass_apply => Physics.SplitWeylMass.mass_apply,
  GUT.SplitWeylMass.mass_nonzero => Physics.SplitWeylMass.mass_nonzero,
  GUT.SplitWeylMass.mass_pair => Physics.SplitWeylMass.mass_pair,
  GUT.SplitWeylMass.mem_radical_iff => Physics.SplitWeylMass.mem_radical_iff,
  GUT.SplitWeylMass.radicalEquiv => Physics.SplitWeylMass.radicalEquiv,
  GUT.SplitWeylMass.radicalLinearEquiv => Physics.SplitWeylMass.radicalLinearEquiv,
  GUT.SplitWeylMass.radical_character => Physics.SplitWeylMass.radical_character,
  GUT.SplitWeylMass.radical_finrank => Physics.SplitWeylMass.radical_finrank,
  GUT.SplitWeylMass.representation => Physics.SplitWeylMass.representation
]

assert_compatible GUT.SplitWeylMass.Fields => Physics.SplitWeylMass.Fields
assert_compatible GUT.SplitWeylMass.mass => Physics.SplitWeylMass.mass
assert_compatible GUT.SplitWeylMass.mass_apply => Physics.SplitWeylMass.mass_apply
assert_compatible GUT.SplitWeylMass.mass_nonzero => Physics.SplitWeylMass.mass_nonzero
assert_compatible GUT.SplitWeylMass.mass_pair => Physics.SplitWeylMass.mass_pair
assert_compatible GUT.SplitWeylMass.mem_radical_iff => Physics.SplitWeylMass.mem_radical_iff
assert_compatible GUT.SplitWeylMass.radicalEquiv => Physics.SplitWeylMass.radicalEquiv
assert_compatible GUT.SplitWeylMass.radicalLinearEquiv => Physics.SplitWeylMass.radicalLinearEquiv
assert_compatible GUT.SplitWeylMass.radical_character => Physics.SplitWeylMass.radical_character
assert_compatible GUT.SplitWeylMass.radical_finrank => Physics.SplitWeylMass.radical_finrank
assert_compatible GUT.SplitWeylMass.representation => Physics.SplitWeylMass.representation
