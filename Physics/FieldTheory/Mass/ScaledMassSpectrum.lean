import Physics.FieldTheory.Mass.Spectrum.ScaledMassSpectrum
import Physics.FieldTheory.Mass.InvariantWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.ScaledMassSpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScaledMassSpectrum.form_nonzero => Physics.ScaledMassSpectrum.form_nonzero,
  GUT.ScaledMassSpectrum.mass => Physics.ScaledMassSpectrum.mass,
  GUT.ScaledMassSpectrum.mass.eq_1 => Physics.ScaledMassSpectrum.mass.eq_1,
  GUT.ScaledMassSpectrum.mass_apply => Physics.ScaledMassSpectrum.mass_apply,
  GUT.ScaledMassSpectrum.mem_radical_iff => Physics.ScaledMassSpectrum.mem_radical_iff,
  GUT.ScaledMassSpectrum.one_mass => Physics.ScaledMassSpectrum.one_mass,
  GUT.ScaledMassSpectrum.radicalEquiv => Physics.ScaledMassSpectrum.radicalEquiv,
  GUT.ScaledMassSpectrum.radical_character => Physics.ScaledMassSpectrum.radical_character,
  GUT.ScaledMassSpectrum.radical_finrank => Physics.ScaledMassSpectrum.radical_finrank,
  GUT.ScaledMassSpectrum.zero_mass => Physics.ScaledMassSpectrum.zero_mass
]

assert_compatible GUT.ScaledMassSpectrum.form_nonzero => Physics.ScaledMassSpectrum.form_nonzero
assert_compatible GUT.ScaledMassSpectrum.mass => Physics.ScaledMassSpectrum.mass
assert_compatible GUT.ScaledMassSpectrum.mass.eq_1 => Physics.ScaledMassSpectrum.mass.eq_1
assert_compatible GUT.ScaledMassSpectrum.mass_apply => Physics.ScaledMassSpectrum.mass_apply
assert_compatible GUT.ScaledMassSpectrum.mem_radical_iff => Physics.ScaledMassSpectrum.mem_radical_iff
assert_compatible GUT.ScaledMassSpectrum.one_mass => Physics.ScaledMassSpectrum.one_mass
assert_compatible GUT.ScaledMassSpectrum.radicalEquiv => Physics.ScaledMassSpectrum.radicalEquiv
assert_compatible GUT.ScaledMassSpectrum.radical_character => Physics.ScaledMassSpectrum.radical_character
assert_compatible GUT.ScaledMassSpectrum.radical_finrank => Physics.ScaledMassSpectrum.radical_finrank
assert_compatible GUT.ScaledMassSpectrum.zero_mass => Physics.ScaledMassSpectrum.zero_mass
