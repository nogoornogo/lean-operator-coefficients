import Physics.FieldTheory.Mass.Spectrum.Audit.AuditAbelianMassSpectrum
import Physics.FieldTheory.Mass.AbelianMassSpectrum
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Spectrum.Audit.AuditAbelianMassSpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AuditAbelianMassSpectrum.PairSpace => Physics.AuditAbelianMassSpectrum.PairSpace,
  GUT.AuditAbelianMassSpectrum.circleTarget => Physics.AuditAbelianMassSpectrum.circleTarget,
  GUT.AuditAbelianMassSpectrum.circleTarget.eq_1 => Physics.AuditAbelianMassSpectrum.circleTarget.eq_1,
  GUT.AuditAbelianMassSpectrum.circle_character_not_self_dual => Physics.AuditAbelianMassSpectrum.circle_character_not_self_dual,
  GUT.AuditAbelianMassSpectrum.circle_negative => Physics.AuditAbelianMassSpectrum.circle_negative,
  GUT.AuditAbelianMassSpectrum.circle_positive => Physics.AuditAbelianMassSpectrum.circle_positive,
  GUT.AuditAbelianMassSpectrum.circle_target_character => Physics.AuditAbelianMassSpectrum.circle_target_character,
  GUT.AuditAbelianMassSpectrum.imaginaryUnit => Physics.AuditAbelianMassSpectrum.imaginaryUnit,
  GUT.AuditAbelianMassSpectrum.negative_coefficient_has_no_mode => Physics.AuditAbelianMassSpectrum.negative_coefficient_has_no_mode,
  GUT.AuditAbelianMassSpectrum.nonzero_mass_positive_mode => Physics.AuditAbelianMassSpectrum.nonzero_mass_positive_mode,
  GUT.AuditAbelianMassSpectrum.pairAction => Physics.AuditAbelianMassSpectrum.pairAction,
  GUT.AuditAbelianMassSpectrum.pairAction.eq_1 => Physics.AuditAbelianMassSpectrum.pairAction.eq_1,
  GUT.AuditAbelianMassSpectrum.pairEquiv => Physics.AuditAbelianMassSpectrum.pairEquiv,
  GUT.AuditAbelianMassSpectrum.pairMass => Physics.AuditAbelianMassSpectrum.pairMass,
  GUT.AuditAbelianMassSpectrum.pairMass_nonzero => Physics.AuditAbelianMassSpectrum.pairMass_nonzero,
  GUT.AuditAbelianMassSpectrum.pair_character => Physics.AuditAbelianMassSpectrum.pair_character,
  GUT.AuditAbelianMassSpectrum.pair_target_character => Physics.AuditAbelianMassSpectrum.pair_target_character,
  GUT.AuditAbelianMassSpectrum.pair_unitary => Physics.AuditAbelianMassSpectrum.pair_unitary,
  GUT.AuditAbelianMassSpectrum.scalar => Physics.AuditAbelianMassSpectrum.scalar,
  GUT.AuditAbelianMassSpectrum.scalar_character => Physics.AuditAbelianMassSpectrum.scalar_character,
  GUT.AuditAbelianMassSpectrum.scalar_spectrum => Physics.AuditAbelianMassSpectrum.scalar_spectrum,
  GUT.AuditAbelianMassSpectrum.scalar_unitary => Physics.AuditAbelianMassSpectrum.scalar_unitary,
  GUT.AuditAbelianMassSpectrum.secondCoordinate => Physics.AuditAbelianMassSpectrum.secondCoordinate,
  GUT.AuditAbelianMassSpectrum.signCharacter => Physics.AuditAbelianMassSpectrum.signCharacter,
  GUT.AuditAbelianMassSpectrum.signMass => Physics.AuditAbelianMassSpectrum.signMass,
  GUT.AuditAbelianMassSpectrum.signMass.eq_1 => Physics.AuditAbelianMassSpectrum.signMass.eq_1,
  GUT.AuditAbelianMassSpectrum.signMass_nonzero => Physics.AuditAbelianMassSpectrum.signMass_nonzero,
  GUT.AuditAbelianMassSpectrum.signMass_radical_zero => Physics.AuditAbelianMassSpectrum.signMass_radical_zero,
  GUT.AuditAbelianMassSpectrum.sign_dual_index_zero => Physics.AuditAbelianMassSpectrum.sign_dual_index_zero,
  GUT.AuditAbelianMassSpectrum.sign_self_dual => Physics.AuditAbelianMassSpectrum.sign_self_dual,
  GUT.AuditAbelianMassSpectrum.zero_mass_positive_mode => Physics.AuditAbelianMassSpectrum.zero_mass_positive_mode
]

assert_compatible GUT.AuditAbelianMassSpectrum.PairSpace => Physics.AuditAbelianMassSpectrum.PairSpace
assert_compatible GUT.AuditAbelianMassSpectrum.circleTarget => Physics.AuditAbelianMassSpectrum.circleTarget
assert_compatible GUT.AuditAbelianMassSpectrum.circleTarget.eq_1 => Physics.AuditAbelianMassSpectrum.circleTarget.eq_1
assert_compatible GUT.AuditAbelianMassSpectrum.circle_character_not_self_dual => Physics.AuditAbelianMassSpectrum.circle_character_not_self_dual
assert_compatible GUT.AuditAbelianMassSpectrum.circle_negative => Physics.AuditAbelianMassSpectrum.circle_negative
assert_compatible GUT.AuditAbelianMassSpectrum.circle_positive => Physics.AuditAbelianMassSpectrum.circle_positive
assert_compatible GUT.AuditAbelianMassSpectrum.circle_target_character => Physics.AuditAbelianMassSpectrum.circle_target_character
assert_compatible GUT.AuditAbelianMassSpectrum.imaginaryUnit => Physics.AuditAbelianMassSpectrum.imaginaryUnit
assert_compatible GUT.AuditAbelianMassSpectrum.negative_coefficient_has_no_mode => Physics.AuditAbelianMassSpectrum.negative_coefficient_has_no_mode
assert_compatible GUT.AuditAbelianMassSpectrum.nonzero_mass_positive_mode => Physics.AuditAbelianMassSpectrum.nonzero_mass_positive_mode
assert_compatible GUT.AuditAbelianMassSpectrum.pairAction => Physics.AuditAbelianMassSpectrum.pairAction
assert_compatible GUT.AuditAbelianMassSpectrum.pairAction.eq_1 => Physics.AuditAbelianMassSpectrum.pairAction.eq_1
assert_compatible GUT.AuditAbelianMassSpectrum.pairEquiv => Physics.AuditAbelianMassSpectrum.pairEquiv
assert_compatible GUT.AuditAbelianMassSpectrum.pairMass => Physics.AuditAbelianMassSpectrum.pairMass
assert_compatible GUT.AuditAbelianMassSpectrum.pairMass_nonzero => Physics.AuditAbelianMassSpectrum.pairMass_nonzero
assert_compatible GUT.AuditAbelianMassSpectrum.pair_character => Physics.AuditAbelianMassSpectrum.pair_character
assert_compatible GUT.AuditAbelianMassSpectrum.pair_target_character => Physics.AuditAbelianMassSpectrum.pair_target_character
assert_compatible GUT.AuditAbelianMassSpectrum.pair_unitary => Physics.AuditAbelianMassSpectrum.pair_unitary
assert_compatible GUT.AuditAbelianMassSpectrum.scalar => Physics.AuditAbelianMassSpectrum.scalar
assert_compatible GUT.AuditAbelianMassSpectrum.scalar_character => Physics.AuditAbelianMassSpectrum.scalar_character
assert_compatible GUT.AuditAbelianMassSpectrum.scalar_spectrum => Physics.AuditAbelianMassSpectrum.scalar_spectrum
assert_compatible GUT.AuditAbelianMassSpectrum.scalar_unitary => Physics.AuditAbelianMassSpectrum.scalar_unitary
assert_compatible GUT.AuditAbelianMassSpectrum.secondCoordinate => Physics.AuditAbelianMassSpectrum.secondCoordinate
assert_compatible GUT.AuditAbelianMassSpectrum.signCharacter => Physics.AuditAbelianMassSpectrum.signCharacter
assert_compatible GUT.AuditAbelianMassSpectrum.signMass => Physics.AuditAbelianMassSpectrum.signMass
assert_compatible GUT.AuditAbelianMassSpectrum.signMass.eq_1 => Physics.AuditAbelianMassSpectrum.signMass.eq_1
assert_compatible GUT.AuditAbelianMassSpectrum.signMass_nonzero => Physics.AuditAbelianMassSpectrum.signMass_nonzero
assert_compatible GUT.AuditAbelianMassSpectrum.signMass_radical_zero => Physics.AuditAbelianMassSpectrum.signMass_radical_zero
assert_compatible GUT.AuditAbelianMassSpectrum.sign_dual_index_zero => Physics.AuditAbelianMassSpectrum.sign_dual_index_zero
assert_compatible GUT.AuditAbelianMassSpectrum.sign_self_dual => Physics.AuditAbelianMassSpectrum.sign_self_dual
assert_compatible GUT.AuditAbelianMassSpectrum.zero_mass_positive_mode => Physics.AuditAbelianMassSpectrum.zero_mass_positive_mode
