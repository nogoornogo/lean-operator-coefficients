import Physics.StandardModel.Spectrum.Representations.Audit.AuditFourWeightQque
import Physics.StandardModel.Spectrum.FourWeightQque
import Physics.StandardModel.Spectrum.ConjugationTrialityObstruction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.Audit.AuditFourWeightQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourWeightControls.four_target_not_fifteen => Physics.FourWeightControls.four_target_not_fifteen,
  GUT.FourWeightControls.neutralProfiles => Physics.FourWeightControls.neutralProfiles,
  GUT.FourWeightControls.neutralProfiles.eq_1 => Physics.FourWeightControls.neutralProfiles.eq_1,
  GUT.FourWeightControls.spectatorProfiles => Physics.FourWeightControls.spectatorProfiles,
  GUT.FourWeightControls.spectatorProfiles.eq_1 => Physics.FourWeightControls.spectatorProfiles.eq_1,
  GUT.FourWeightControls.triality_no_two => Physics.FourWeightControls.triality_no_two,
  GUT.FourWeightControls.zero_spectrum_not_positive_target => Physics.FourWeightControls.zero_spectrum_not_positive_target
]

assert_compatible GUT.FourWeightControls.four_target_not_fifteen => Physics.FourWeightControls.four_target_not_fifteen
assert_compatible GUT.FourWeightControls.neutralProfiles => Physics.FourWeightControls.neutralProfiles
assert_compatible GUT.FourWeightControls.neutralProfiles.eq_1 => Physics.FourWeightControls.neutralProfiles.eq_1
assert_compatible GUT.FourWeightControls.spectatorProfiles => Physics.FourWeightControls.spectatorProfiles
assert_compatible GUT.FourWeightControls.spectatorProfiles.eq_1 => Physics.FourWeightControls.spectatorProfiles.eq_1
assert_compatible GUT.FourWeightControls.triality_no_two => Physics.FourWeightControls.triality_no_two
assert_compatible GUT.FourWeightControls.zero_spectrum_not_positive_target => Physics.FourWeightControls.zero_spectrum_not_positive_target
