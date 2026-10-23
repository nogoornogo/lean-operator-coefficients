import Physics.StandardModel.Spectrum.Mass.ConjugationMassSource
import Physics.StandardModel.Spectrum.RestrictedConjugationMassSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Mass.ConjugationMassSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StructuralConjugationMass.chargesSupported => Physics.StructuralConjugationMass.chargesSupported,
  GUT.StructuralConjugationMass.chiral_spectrum => Physics.StructuralConjugationMass.chiral_spectrum,
  GUT.StructuralConjugationMass.exists_actual_signature_pair => Physics.StructuralConjugationMass.exists_actual_signature_pair,
  GUT.StructuralConjugationMass.exists_zeroMode => Physics.StructuralConjugationMass.exists_zeroMode,
  GUT.StructuralConjugationMass.restricted_unitary => Physics.StructuralConjugationMass.restricted_unitary,
  GUT.StructuralConjugationMass.selection_rule_obstruction => Physics.StructuralConjugationMass.selection_rule_obstruction,
  GUT.StructuralConjugationMass.spectrum => Physics.StructuralConjugationMass.spectrum,
  GUT.StructuralConjugationMass.spectrum_eq_restricted => Physics.StructuralConjugationMass.spectrum_eq_restricted,
  GUT.StructuralConjugationMass.spectrum_nonneg => Physics.StructuralConjugationMass.spectrum_nonneg
]

assert_compatible GUT.StructuralConjugationMass.chargesSupported => Physics.StructuralConjugationMass.chargesSupported
assert_compatible GUT.StructuralConjugationMass.chiral_spectrum => Physics.StructuralConjugationMass.chiral_spectrum
assert_compatible GUT.StructuralConjugationMass.exists_actual_signature_pair => Physics.StructuralConjugationMass.exists_actual_signature_pair
assert_compatible GUT.StructuralConjugationMass.exists_zeroMode => Physics.StructuralConjugationMass.exists_zeroMode
assert_compatible GUT.StructuralConjugationMass.restricted_unitary => Physics.StructuralConjugationMass.restricted_unitary
assert_compatible GUT.StructuralConjugationMass.selection_rule_obstruction => Physics.StructuralConjugationMass.selection_rule_obstruction
assert_compatible GUT.StructuralConjugationMass.spectrum => Physics.StructuralConjugationMass.spectrum
assert_compatible GUT.StructuralConjugationMass.spectrum_eq_restricted => Physics.StructuralConjugationMass.spectrum_eq_restricted
assert_compatible GUT.StructuralConjugationMass.spectrum_nonneg => Physics.StructuralConjugationMass.spectrum_nonneg
