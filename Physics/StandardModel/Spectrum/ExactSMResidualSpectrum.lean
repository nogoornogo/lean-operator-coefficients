import Physics.StandardModel.Spectrum.Representations.ExactSMResidualSpectrum
import Physics.StandardModel.Spectrum.ExactSMSpectrum
import Physics.StandardModel.Spectrum.LightSMSpeciesIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.ExactSMResidualSpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ExactSMResidualSpectrum.Carrier => Physics.ExactSMResidualSpectrum.Carrier,
  GUT.ExactSMResidualSpectrum.TargetSpace => Physics.ExactSMResidualSpectrum.TargetSpace,
  GUT.ExactSMResidualSpectrum.carrierAdd => Physics.ExactSMResidualSpectrum.carrierAdd,
  GUT.ExactSMResidualSpectrum.carrierFinite => Physics.ExactSMResidualSpectrum.carrierFinite,
  GUT.ExactSMResidualSpectrum.carrierModule => Physics.ExactSMResidualSpectrum.carrierModule,
  GUT.ExactSMResidualSpectrum.gauge => Physics.ExactSMResidualSpectrum.gauge,
  GUT.ExactSMResidualSpectrum.has_species_target => Physics.ExactSMResidualSpectrum.has_species_target,
  GUT.ExactSMResidualSpectrum.index_eq_character_of_opposite_zero => Physics.ExactSMResidualSpectrum.index_eq_character_of_opposite_zero,
  GUT.ExactSMResidualSpectrum.species_indices => Physics.ExactSMResidualSpectrum.species_indices,
  GUT.ExactSMResidualSpectrum.target => Physics.ExactSMResidualSpectrum.target,
  GUT.ExactSMResidualSpectrum.targetNormedAddCommGroup => Physics.ExactSMResidualSpectrum.targetNormedAddCommGroup,
  GUT.ExactSMResidualSpectrum.targetNormedSpace => Physics.ExactSMResidualSpectrum.targetNormedSpace,
  GUT.ExactSMResidualSpectrum.target_continuous => Physics.ExactSMResidualSpectrum.target_continuous,
  GUT.ExactSMResidualSpectrum.target_finrank => Physics.ExactSMResidualSpectrum.target_finrank,
  GUT.ExactSMResidualSpectrum.target_nontrivial => Physics.ExactSMResidualSpectrum.target_nontrivial
]

assert_compatible GUT.ExactSMResidualSpectrum.Carrier => Physics.ExactSMResidualSpectrum.Carrier
assert_compatible GUT.ExactSMResidualSpectrum.TargetSpace => Physics.ExactSMResidualSpectrum.TargetSpace
assert_compatible GUT.ExactSMResidualSpectrum.carrierAdd => Physics.ExactSMResidualSpectrum.carrierAdd
assert_compatible GUT.ExactSMResidualSpectrum.carrierFinite => Physics.ExactSMResidualSpectrum.carrierFinite
assert_compatible GUT.ExactSMResidualSpectrum.carrierModule => Physics.ExactSMResidualSpectrum.carrierModule
assert_compatible GUT.ExactSMResidualSpectrum.gauge => Physics.ExactSMResidualSpectrum.gauge
assert_compatible GUT.ExactSMResidualSpectrum.has_species_target => Physics.ExactSMResidualSpectrum.has_species_target
assert_compatible GUT.ExactSMResidualSpectrum.index_eq_character_of_opposite_zero => Physics.ExactSMResidualSpectrum.index_eq_character_of_opposite_zero
assert_compatible GUT.ExactSMResidualSpectrum.species_indices => Physics.ExactSMResidualSpectrum.species_indices
assert_compatible GUT.ExactSMResidualSpectrum.target => Physics.ExactSMResidualSpectrum.target
assert_compatible GUT.ExactSMResidualSpectrum.targetNormedAddCommGroup => Physics.ExactSMResidualSpectrum.targetNormedAddCommGroup
assert_compatible GUT.ExactSMResidualSpectrum.targetNormedSpace => Physics.ExactSMResidualSpectrum.targetNormedSpace
assert_compatible GUT.ExactSMResidualSpectrum.target_continuous => Physics.ExactSMResidualSpectrum.target_continuous
assert_compatible GUT.ExactSMResidualSpectrum.target_finrank => Physics.ExactSMResidualSpectrum.target_finrank
assert_compatible GUT.ExactSMResidualSpectrum.target_nontrivial => Physics.ExactSMResidualSpectrum.target_nontrivial
