import Physics.StandardModel.Operators.Selection.LeptonTriality
import Physics.StandardModel.Operators.StandardModelLocalOperator
import Physics.StandardModel.Spectrum.FiniteChargeProfiles
import Physics.StandardModel.Gauge.ResidualGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.LeptonTriality instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LeptonTriality.Residual => Physics.LeptonTriality.Residual,
  GUT.LeptonTriality.assignment => Physics.LeptonTriality.assignment,
  GUT.LeptonTriality.assignment_characters => Physics.LeptonTriality.assignment_characters,
  GUT.LeptonTriality.assignment_supported => Physics.LeptonTriality.assignment_supported,
  GUT.LeptonTriality.canonical_tensors_not_invariant => Physics.LeptonTriality.canonical_tensors_not_invariant,
  GUT.LeptonTriality.character => Physics.LeptonTriality.character,
  GUT.LeptonTriality.character.eq_1 => Physics.LeptonTriality.character.eq_1,
  GUT.LeptonTriality.character_injective => Physics.LeptonTriality.character_injective,
  GUT.LeptonTriality.character_ne_one => Physics.LeptonTriality.character_ne_one,
  GUT.LeptonTriality.charges => Physics.LeptonTriality.charges,
  GUT.LeptonTriality.charges.eq_1 => Physics.LeptonTriality.charges.eq_1,
  GUT.LeptonTriality.charges_not_orbitCompatible => Physics.LeptonTriality.charges_not_orbitCompatible,
  GUT.LeptonTriality.cyclic_charge_counterexample => Physics.LeptonTriality.cyclic_charge_counterexample,
  GUT.LeptonTriality.family => Physics.LeptonTriality.family,
  GUT.LeptonTriality.forbids_all_supported => Physics.LeptonTriality.forbids_all_supported,
  GUT.LeptonTriality.label => Physics.LeptonTriality.label,
  GUT.LeptonTriality.label_ne_zero => Physics.LeptonTriality.label_ne_zero,
  GUT.LeptonTriality.label_three_nsmul => Physics.LeptonTriality.label_three_nsmul,
  GUT.LeptonTriality.not_universal_family_obstruction => Physics.LeptonTriality.not_universal_family_obstruction,
  GUT.LeptonTriality.protonFirst_charges => Physics.LeptonTriality.protonFirst_charges,
  GUT.LeptonTriality.protonSecond_charges => Physics.LeptonTriality.protonSecond_charges,
  GUT.LeptonTriality.spectrum => Physics.LeptonTriality.spectrum,
  GUT.LeptonTriality.spectrum_forgetting => Physics.LeptonTriality.spectrum_forgetting,
  GUT.LeptonTriality.spectrum_not_weylInvariant => Physics.LeptonTriality.spectrum_not_weylInvariant,
  GUT.LeptonTriality.supported_iff => Physics.LeptonTriality.supported_iff,
  GUT.LeptonTriality.supported_spectrum_counterexample => Physics.LeptonTriality.supported_spectrum_counterexample
]

assert_compatible GUT.LeptonTriality.Residual => Physics.LeptonTriality.Residual
assert_compatible GUT.LeptonTriality.assignment => Physics.LeptonTriality.assignment
assert_compatible GUT.LeptonTriality.assignment_characters => Physics.LeptonTriality.assignment_characters
assert_compatible GUT.LeptonTriality.assignment_supported => Physics.LeptonTriality.assignment_supported
assert_compatible GUT.LeptonTriality.canonical_tensors_not_invariant => Physics.LeptonTriality.canonical_tensors_not_invariant
assert_compatible GUT.LeptonTriality.character => Physics.LeptonTriality.character
assert_compatible GUT.LeptonTriality.character.eq_1 => Physics.LeptonTriality.character.eq_1
assert_compatible GUT.LeptonTriality.character_injective => Physics.LeptonTriality.character_injective
assert_compatible GUT.LeptonTriality.character_ne_one => Physics.LeptonTriality.character_ne_one
assert_compatible GUT.LeptonTriality.charges => Physics.LeptonTriality.charges
assert_compatible GUT.LeptonTriality.charges.eq_1 => Physics.LeptonTriality.charges.eq_1
assert_compatible GUT.LeptonTriality.charges_not_orbitCompatible => Physics.LeptonTriality.charges_not_orbitCompatible
assert_compatible GUT.LeptonTriality.cyclic_charge_counterexample => Physics.LeptonTriality.cyclic_charge_counterexample
assert_compatible GUT.LeptonTriality.family => Physics.LeptonTriality.family
assert_compatible GUT.LeptonTriality.forbids_all_supported => Physics.LeptonTriality.forbids_all_supported
assert_compatible GUT.LeptonTriality.label => Physics.LeptonTriality.label
assert_compatible GUT.LeptonTriality.label_ne_zero => Physics.LeptonTriality.label_ne_zero
assert_compatible GUT.LeptonTriality.label_three_nsmul => Physics.LeptonTriality.label_three_nsmul
assert_compatible GUT.LeptonTriality.not_universal_family_obstruction => Physics.LeptonTriality.not_universal_family_obstruction
assert_compatible GUT.LeptonTriality.protonFirst_charges => Physics.LeptonTriality.protonFirst_charges
assert_compatible GUT.LeptonTriality.protonSecond_charges => Physics.LeptonTriality.protonSecond_charges
assert_compatible GUT.LeptonTriality.spectrum => Physics.LeptonTriality.spectrum
assert_compatible GUT.LeptonTriality.spectrum_forgetting => Physics.LeptonTriality.spectrum_forgetting
assert_compatible GUT.LeptonTriality.spectrum_not_weylInvariant => Physics.LeptonTriality.spectrum_not_weylInvariant
assert_compatible GUT.LeptonTriality.supported_iff => Physics.LeptonTriality.supported_iff
assert_compatible GUT.LeptonTriality.supported_spectrum_counterexample => Physics.LeptonTriality.supported_spectrum_counterexample
