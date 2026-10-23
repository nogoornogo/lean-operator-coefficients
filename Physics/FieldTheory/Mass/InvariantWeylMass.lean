import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Physics.FieldTheory.Mass.DiracWeylConvention
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.InvariantWeylMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InvariantWeylMass.dualIndex => Physics.InvariantWeylMass.dualIndex,
  GUT.InvariantWeylMass.dualIndex.congr_simp => Physics.InvariantWeylMass.dualIndex.congr_simp,
  GUT.InvariantWeylMass.dualIndex.eq_1 => Physics.InvariantWeylMass.dualIndex.eq_1,
  GUT.InvariantWeylMass.dualIndex_character => Physics.InvariantWeylMass.dualIndex_character,
  GUT.InvariantWeylMass.lightDualIndex => Physics.InvariantWeylMass.lightDualIndex,
  GUT.InvariantWeylMass.lightDualIndex.eq_1 => Physics.InvariantWeylMass.lightDualIndex.eq_1,
  GUT.InvariantWeylMass.lightDualIndex_characterEquivalent_ultravioletDualIndex => Physics.InvariantWeylMass.lightDualIndex_characterEquivalent_ultravioletDualIndex,
  GUT.InvariantWeylMass.ofDirac => Physics.InvariantWeylMass.ofDirac,
  GUT.InvariantWeylMass.ofDirac_dual_character_eq_signed_antisymmetrization => Physics.InvariantWeylMass.ofDirac_dual_character_eq_signed_antisymmetrization,
  GUT.InvariantWeylMass.ofDirac_radical => Physics.InvariantWeylMass.ofDirac_radical,
  GUT.InvariantWeylMass.ofDirac_radical_dual_character_eq_lightIndex_antisymmetrization => Physics.InvariantWeylMass.ofDirac_radical_dual_character_eq_lightIndex_antisymmetrization,
  GUT.InvariantWeylMass.radical_dual_character_eq => Physics.InvariantWeylMass.radical_dual_character_eq,
  GUT.InvariantWeylMass.ultravioletDualIndex_characterEquivalent_of_lightDualIndex => Physics.InvariantWeylMass.ultravioletDualIndex_characterEquivalent_of_lightDualIndex
]

assert_compatible GUT.InvariantWeylMass.dualIndex => Physics.InvariantWeylMass.dualIndex
assert_compatible GUT.InvariantWeylMass.dualIndex.congr_simp => Physics.InvariantWeylMass.dualIndex.congr_simp
assert_compatible GUT.InvariantWeylMass.dualIndex.eq_1 => Physics.InvariantWeylMass.dualIndex.eq_1
assert_compatible GUT.InvariantWeylMass.dualIndex_character => Physics.InvariantWeylMass.dualIndex_character
assert_compatible GUT.InvariantWeylMass.lightDualIndex => Physics.InvariantWeylMass.lightDualIndex
assert_compatible GUT.InvariantWeylMass.lightDualIndex.eq_1 => Physics.InvariantWeylMass.lightDualIndex.eq_1
assert_compatible GUT.InvariantWeylMass.lightDualIndex_characterEquivalent_ultravioletDualIndex => Physics.InvariantWeylMass.lightDualIndex_characterEquivalent_ultravioletDualIndex
assert_compatible GUT.InvariantWeylMass.ofDirac => Physics.InvariantWeylMass.ofDirac
assert_compatible GUT.InvariantWeylMass.ofDirac_dual_character_eq_signed_antisymmetrization => Physics.InvariantWeylMass.ofDirac_dual_character_eq_signed_antisymmetrization
assert_compatible GUT.InvariantWeylMass.ofDirac_radical => Physics.InvariantWeylMass.ofDirac_radical
assert_compatible GUT.InvariantWeylMass.ofDirac_radical_dual_character_eq_lightIndex_antisymmetrization => Physics.InvariantWeylMass.ofDirac_radical_dual_character_eq_lightIndex_antisymmetrization
assert_compatible GUT.InvariantWeylMass.radical_dual_character_eq => Physics.InvariantWeylMass.radical_dual_character_eq
assert_compatible GUT.InvariantWeylMass.ultravioletDualIndex_characterEquivalent_of_lightDualIndex => Physics.InvariantWeylMass.ultravioletDualIndex_characterEquivalent_of_lightDualIndex
