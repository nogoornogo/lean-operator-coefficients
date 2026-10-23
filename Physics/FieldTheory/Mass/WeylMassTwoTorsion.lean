import Physics.FieldTheory.Mass.Algebra.WeylMassTwoTorsion
import Physics.FieldTheory.Mass.InvariantWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.WeylMassTwoTorsion instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylMassTwoTorsion.majoranaMass => Physics.WeylMassTwoTorsion.majoranaMass,
  GUT.WeylMassTwoTorsion.majoranaMass.eq_1 => Physics.WeylMassTwoTorsion.majoranaMass.eq_1,
  GUT.WeylMassTwoTorsion.majoranaMass_nondegenerate => Physics.WeylMassTwoTorsion.majoranaMass_nondegenerate,
  GUT.WeylMassTwoTorsion.majoranaMass_radical_finrank => Physics.WeylMassTwoTorsion.majoranaMass_radical_finrank,
  GUT.WeylMassTwoTorsion.radical_dual_character_zero => Physics.WeylMassTwoTorsion.radical_dual_character_zero,
  GUT.WeylMassTwoTorsion.same_dual_index_different_zero_modes => Physics.WeylMassTwoTorsion.same_dual_index_different_zero_modes,
  GUT.WeylMassTwoTorsion.signGroup_card => Physics.WeylMassTwoTorsion.signGroup_card,
  GUT.WeylMassTwoTorsion.signRepresentation => Physics.WeylMassTwoTorsion.signRepresentation,
  GUT.WeylMassTwoTorsion.signRepresentation_apply => Physics.WeylMassTwoTorsion.signRepresentation_apply,
  GUT.WeylMassTwoTorsion.signRepresentation_nontrivial => Physics.WeylMassTwoTorsion.signRepresentation_nontrivial,
  GUT.WeylMassTwoTorsion.signRepresentation_unitary => Physics.WeylMassTwoTorsion.signRepresentation_unitary,
  GUT.WeylMassTwoTorsion.sign_dual_character_zero => Physics.WeylMassTwoTorsion.sign_dual_character_zero,
  GUT.WeylMassTwoTorsion.zero_mass_radical_finrank => Physics.WeylMassTwoTorsion.zero_mass_radical_finrank
]

assert_compatible GUT.WeylMassTwoTorsion.majoranaMass => Physics.WeylMassTwoTorsion.majoranaMass
assert_compatible GUT.WeylMassTwoTorsion.majoranaMass.eq_1 => Physics.WeylMassTwoTorsion.majoranaMass.eq_1
assert_compatible GUT.WeylMassTwoTorsion.majoranaMass_nondegenerate => Physics.WeylMassTwoTorsion.majoranaMass_nondegenerate
assert_compatible GUT.WeylMassTwoTorsion.majoranaMass_radical_finrank => Physics.WeylMassTwoTorsion.majoranaMass_radical_finrank
assert_compatible GUT.WeylMassTwoTorsion.radical_dual_character_zero => Physics.WeylMassTwoTorsion.radical_dual_character_zero
assert_compatible GUT.WeylMassTwoTorsion.same_dual_index_different_zero_modes => Physics.WeylMassTwoTorsion.same_dual_index_different_zero_modes
assert_compatible GUT.WeylMassTwoTorsion.signGroup_card => Physics.WeylMassTwoTorsion.signGroup_card
assert_compatible GUT.WeylMassTwoTorsion.signRepresentation => Physics.WeylMassTwoTorsion.signRepresentation
assert_compatible GUT.WeylMassTwoTorsion.signRepresentation_apply => Physics.WeylMassTwoTorsion.signRepresentation_apply
assert_compatible GUT.WeylMassTwoTorsion.signRepresentation_nontrivial => Physics.WeylMassTwoTorsion.signRepresentation_nontrivial
assert_compatible GUT.WeylMassTwoTorsion.signRepresentation_unitary => Physics.WeylMassTwoTorsion.signRepresentation_unitary
assert_compatible GUT.WeylMassTwoTorsion.sign_dual_character_zero => Physics.WeylMassTwoTorsion.sign_dual_character_zero
assert_compatible GUT.WeylMassTwoTorsion.zero_mass_radical_finrank => Physics.WeylMassTwoTorsion.zero_mass_radical_finrank
