import Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.AbelianMassSpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AbelianMassSpectrum.coefficient_lower_bound => Physics.AbelianMassSpectrum.coefficient_lower_bound,
  GUT.AbelianMassSpectrum.exists_radical_vector_of_pos => Physics.AbelianMassSpectrum.exists_radical_vector_of_pos,
  GUT.AbelianMassSpectrum.exists_zeroMode_of_pos => Physics.AbelianMassSpectrum.exists_zeroMode_of_pos,
  GUT.AbelianMassSpectrum.radicalSpectrum => Physics.AbelianMassSpectrum.radicalSpectrum,
  GUT.AbelianMassSpectrum.radicalSpectrum.congr_simp => Physics.AbelianMassSpectrum.radicalSpectrum.congr_simp,
  GUT.AbelianMassSpectrum.radicalSpectrum_eval => Physics.AbelianMassSpectrum.radicalSpectrum_eval,
  GUT.AbelianMassSpectrum.radicalSpectrum_nonneg => Physics.AbelianMassSpectrum.radicalSpectrum_nonneg,
  GUT.AbelianMassSpectrum.radical_dual_spectrum_eq => Physics.AbelianMassSpectrum.radical_dual_spectrum_eq,
  GUT.AbelianMassSpectrum.radical_dual_spectrum_eq_target => Physics.AbelianMassSpectrum.radical_dual_spectrum_eq_target,
  GUT.AbelianMassSpectrum.radical_unitary => Physics.AbelianMassSpectrum.radical_unitary,
  GUT.AbelianMassSpectrum.source_target_of_radical_target => Physics.AbelianMassSpectrum.source_target_of_radical_target
]

assert_compatible GUT.AbelianMassSpectrum.coefficient_lower_bound => Physics.AbelianMassSpectrum.coefficient_lower_bound
assert_compatible GUT.AbelianMassSpectrum.exists_radical_vector_of_pos => Physics.AbelianMassSpectrum.exists_radical_vector_of_pos
assert_compatible GUT.AbelianMassSpectrum.exists_zeroMode_of_pos => Physics.AbelianMassSpectrum.exists_zeroMode_of_pos
assert_compatible GUT.AbelianMassSpectrum.radicalSpectrum => Physics.AbelianMassSpectrum.radicalSpectrum
assert_compatible GUT.AbelianMassSpectrum.radicalSpectrum.congr_simp => Physics.AbelianMassSpectrum.radicalSpectrum.congr_simp
assert_compatible GUT.AbelianMassSpectrum.radicalSpectrum_eval => Physics.AbelianMassSpectrum.radicalSpectrum_eval
assert_compatible GUT.AbelianMassSpectrum.radicalSpectrum_nonneg => Physics.AbelianMassSpectrum.radicalSpectrum_nonneg
assert_compatible GUT.AbelianMassSpectrum.radical_dual_spectrum_eq => Physics.AbelianMassSpectrum.radical_dual_spectrum_eq
assert_compatible GUT.AbelianMassSpectrum.radical_dual_spectrum_eq_target => Physics.AbelianMassSpectrum.radical_dual_spectrum_eq_target
assert_compatible GUT.AbelianMassSpectrum.radical_unitary => Physics.AbelianMassSpectrum.radical_unitary
assert_compatible GUT.AbelianMassSpectrum.source_target_of_radical_target => Physics.AbelianMassSpectrum.source_target_of_radical_target
