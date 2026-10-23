import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex
import Physics.FieldTheory.Mass.InvariantMassData
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InvariantWeylMass.SymmetricMass.complementQuotientEquiv => Physics.InvariantWeylMass.SymmetricMass.complementQuotientEquiv,
  GUT.InvariantWeylMass.SymmetricMass.form_covariant => Physics.InvariantWeylMass.SymmetricMass.form_covariant,
  GUT.InvariantWeylMass.SymmetricMass.mem_radical => Physics.InvariantWeylMass.SymmetricMass.mem_radical,
  GUT.InvariantWeylMass.SymmetricMass.mk.congr_simp => Physics.InvariantWeylMass.SymmetricMass.mk.congr_simp,
  GUT.InvariantWeylMass.SymmetricMass.quotientForm => Physics.InvariantWeylMass.SymmetricMass.quotientForm,
  GUT.InvariantWeylMass.SymmetricMass.quotientForm_invariant => Physics.InvariantWeylMass.SymmetricMass.quotientForm_invariant,
  GUT.InvariantWeylMass.SymmetricMass.quotientForm_mk => Physics.InvariantWeylMass.SymmetricMass.quotientForm_mk,
  GUT.InvariantWeylMass.SymmetricMass.quotientForm_nondegenerate => Physics.InvariantWeylMass.SymmetricMass.quotientForm_nondegenerate,
  GUT.InvariantWeylMass.SymmetricMass.quotientForm_symmetric => Physics.InvariantWeylMass.SymmetricMass.quotientForm_symmetric,
  GUT.InvariantWeylMass.SymmetricMass.quotientMass => Physics.InvariantWeylMass.SymmetricMass.quotientMass,
  GUT.InvariantWeylMass.SymmetricMass.quotientRepresentation => Physics.InvariantWeylMass.SymmetricMass.quotientRepresentation,
  GUT.InvariantWeylMass.SymmetricMass.quotientSelfDualEquiv => Physics.InvariantWeylMass.SymmetricMass.quotientSelfDualEquiv,
  GUT.InvariantWeylMass.SymmetricMass.quotient_character_eq_dual => Physics.InvariantWeylMass.SymmetricMass.quotient_character_eq_dual,
  GUT.InvariantWeylMass.SymmetricMass.radical => Physics.InvariantWeylMass.SymmetricMass.radical,
  GUT.InvariantWeylMass.SymmetricMass.radical_dual_character_eq => Physics.InvariantWeylMass.SymmetricMass.radical_dual_character_eq,
  GUT.InvariantWeylMass.SymmetricMass.radical_eq_bot_of_nondegenerate => Physics.InvariantWeylMass.SymmetricMass.radical_eq_bot_of_nondegenerate,
  GUT.InvariantWeylMass.SymmetricMass.radical_zero => Physics.InvariantWeylMass.SymmetricMass.radical_zero,
  GUT.InvariantWeylMass.SymmetricMass.toIntertwiningMap => Physics.InvariantWeylMass.SymmetricMass.toIntertwiningMap,
  GUT.InvariantWeylMass.SymmetricMass.zero.eq_1 => Physics.InvariantWeylMass.SymmetricMass.zero.eq_1,
  GUT.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv => Physics.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv,
  GUT.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv_apply => Physics.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv_apply
]

assert_compatible GUT.InvariantWeylMass.SymmetricMass.complementQuotientEquiv => Physics.InvariantWeylMass.SymmetricMass.complementQuotientEquiv
assert_compatible GUT.InvariantWeylMass.SymmetricMass.form_covariant => Physics.InvariantWeylMass.SymmetricMass.form_covariant
assert_compatible GUT.InvariantWeylMass.SymmetricMass.mem_radical => Physics.InvariantWeylMass.SymmetricMass.mem_radical
assert_compatible GUT.InvariantWeylMass.SymmetricMass.mk.congr_simp => Physics.InvariantWeylMass.SymmetricMass.mk.congr_simp
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientForm => Physics.InvariantWeylMass.SymmetricMass.quotientForm
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientForm_invariant => Physics.InvariantWeylMass.SymmetricMass.quotientForm_invariant
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientForm_mk => Physics.InvariantWeylMass.SymmetricMass.quotientForm_mk
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientForm_nondegenerate => Physics.InvariantWeylMass.SymmetricMass.quotientForm_nondegenerate
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientForm_symmetric => Physics.InvariantWeylMass.SymmetricMass.quotientForm_symmetric
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientMass => Physics.InvariantWeylMass.SymmetricMass.quotientMass
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientRepresentation => Physics.InvariantWeylMass.SymmetricMass.quotientRepresentation
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotientSelfDualEquiv => Physics.InvariantWeylMass.SymmetricMass.quotientSelfDualEquiv
assert_compatible GUT.InvariantWeylMass.SymmetricMass.quotient_character_eq_dual => Physics.InvariantWeylMass.SymmetricMass.quotient_character_eq_dual
assert_compatible GUT.InvariantWeylMass.SymmetricMass.radical => Physics.InvariantWeylMass.SymmetricMass.radical
assert_compatible GUT.InvariantWeylMass.SymmetricMass.radical_dual_character_eq => Physics.InvariantWeylMass.SymmetricMass.radical_dual_character_eq
assert_compatible GUT.InvariantWeylMass.SymmetricMass.radical_eq_bot_of_nondegenerate => Physics.InvariantWeylMass.SymmetricMass.radical_eq_bot_of_nondegenerate
assert_compatible GUT.InvariantWeylMass.SymmetricMass.radical_zero => Physics.InvariantWeylMass.SymmetricMass.radical_zero
assert_compatible GUT.InvariantWeylMass.SymmetricMass.toIntertwiningMap => Physics.InvariantWeylMass.SymmetricMass.toIntertwiningMap
assert_compatible GUT.InvariantWeylMass.SymmetricMass.zero.eq_1 => Physics.InvariantWeylMass.SymmetricMass.zero.eq_1
assert_compatible GUT.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv => Physics.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv
assert_compatible GUT.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv_apply => Physics.InvariantWeylMass.SymmetricMass.zeroRadicalEquiv_apply
