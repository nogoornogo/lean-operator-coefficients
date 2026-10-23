import Physics.StandardModel.Spectrum.Charges.LeptonTrialitySpectrum
import Physics.StandardModel.Spectrum.LeptonTrialitySource
import Physics.StandardModel.Spectrum.GaugeTorusTrace
import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Physics.FieldTheory.Mass.AbelianMassSpectrum
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Charges.LeptonTrialitySpectrum instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LeptonTrialitySpectrum.PhysicalGroup => Physics.LeptonTrialitySpectrum.PhysicalGroup,
  GUT.LeptonTrialitySpectrum.actualSpectrum => Physics.LeptonTrialitySpectrum.actualSpectrum,
  GUT.LeptonTrialitySpectrum.actualSpectrum.eq_1 => Physics.LeptonTrialitySpectrum.actualSpectrum.eq_1,
  GUT.LeptonTrialitySpectrum.actualSpectrum_eq => Physics.LeptonTrialitySpectrum.actualSpectrum_eq,
  GUT.LeptonTrialitySpectrum.actual_chiral_index => Physics.LeptonTrialitySpectrum.actual_chiral_index,
  GUT.LeptonTrialitySpectrum.actual_forbids_all_supported => Physics.LeptonTrialitySpectrum.actual_forbids_all_supported,
  GUT.LeptonTrialitySpectrum.actual_not_weylInvariant => Physics.LeptonTrialitySpectrum.actual_not_weylInvariant,
  GUT.LeptonTrialitySpectrum.actual_source_counterexample => Physics.LeptonTrialitySpectrum.actual_source_counterexample,
  GUT.LeptonTrialitySpectrum.actual_supported => Physics.LeptonTrialitySpectrum.actual_supported,
  GUT.LeptonTrialitySpectrum.coordinateMap => Physics.LeptonTrialitySpectrum.coordinateMap,
  GUT.LeptonTrialitySpectrum.coordinateMap.eq_1 => Physics.LeptonTrialitySpectrum.coordinateMap.eq_1,
  GUT.LeptonTrialitySpectrum.eval_lift => Physics.LeptonTrialitySpectrum.eval_lift,
  GUT.LeptonTrialitySpectrum.eval_target_sum => Physics.LeptonTrialitySpectrum.eval_target_sum,
  GUT.LeptonTrialitySpectrum.exists_joint_zeroMode => Physics.LeptonTrialitySpectrum.exists_joint_zeroMode,
  GUT.LeptonTrialitySpectrum.full_spectrum_eq => Physics.LeptonTrialitySpectrum.full_spectrum_eq,
  GUT.LeptonTrialitySpectrum.inclusion => Physics.LeptonTrialitySpectrum.inclusion,
  GUT.LeptonTrialitySpectrum.keyCharacter => Physics.LeptonTrialitySpectrum.keyCharacter,
  GUT.LeptonTrialitySpectrum.keyCharacter.eq_1 => Physics.LeptonTrialitySpectrum.keyCharacter.eq_1,
  GUT.LeptonTrialitySpectrum.keyCharacter_injective => Physics.LeptonTrialitySpectrum.keyCharacter_injective,
  GUT.LeptonTrialitySpectrum.lift => Physics.LeptonTrialitySpectrum.lift,
  GUT.LeptonTrialitySpectrum.lift.eq_1 => Physics.LeptonTrialitySpectrum.lift.eq_1,
  GUT.LeptonTrialitySpectrum.radical_dual_trace => Physics.LeptonTrialitySpectrum.radical_dual_trace,
  GUT.LeptonTrialitySpectrum.radical_trace => Physics.LeptonTrialitySpectrum.radical_trace,
  GUT.LeptonTrialitySpectrum.restricted => Physics.LeptonTrialitySpectrum.restricted,
  GUT.LeptonTrialitySpectrum.restrictedMass => Physics.LeptonTrialitySpectrum.restrictedMass,
  GUT.LeptonTrialitySpectrum.restrictedMass_eq_zero => Physics.LeptonTrialitySpectrum.restrictedMass_eq_zero,
  GUT.LeptonTrialitySpectrum.restricted_unitary => Physics.LeptonTrialitySpectrum.restricted_unitary,
  GUT.LeptonTrialitySpectrum.trace_target => Physics.LeptonTrialitySpectrum.trace_target
]

assert_compatible GUT.LeptonTrialitySpectrum.PhysicalGroup => Physics.LeptonTrialitySpectrum.PhysicalGroup
assert_compatible GUT.LeptonTrialitySpectrum.actualSpectrum => Physics.LeptonTrialitySpectrum.actualSpectrum
assert_compatible GUT.LeptonTrialitySpectrum.actualSpectrum.eq_1 => Physics.LeptonTrialitySpectrum.actualSpectrum.eq_1
assert_compatible GUT.LeptonTrialitySpectrum.actualSpectrum_eq => Physics.LeptonTrialitySpectrum.actualSpectrum_eq
assert_compatible GUT.LeptonTrialitySpectrum.actual_chiral_index => Physics.LeptonTrialitySpectrum.actual_chiral_index
assert_compatible GUT.LeptonTrialitySpectrum.actual_forbids_all_supported => Physics.LeptonTrialitySpectrum.actual_forbids_all_supported
assert_compatible GUT.LeptonTrialitySpectrum.actual_not_weylInvariant => Physics.LeptonTrialitySpectrum.actual_not_weylInvariant
assert_compatible GUT.LeptonTrialitySpectrum.actual_source_counterexample => Physics.LeptonTrialitySpectrum.actual_source_counterexample
assert_compatible GUT.LeptonTrialitySpectrum.actual_supported => Physics.LeptonTrialitySpectrum.actual_supported
assert_compatible GUT.LeptonTrialitySpectrum.coordinateMap => Physics.LeptonTrialitySpectrum.coordinateMap
assert_compatible GUT.LeptonTrialitySpectrum.coordinateMap.eq_1 => Physics.LeptonTrialitySpectrum.coordinateMap.eq_1
assert_compatible GUT.LeptonTrialitySpectrum.eval_lift => Physics.LeptonTrialitySpectrum.eval_lift
assert_compatible GUT.LeptonTrialitySpectrum.eval_target_sum => Physics.LeptonTrialitySpectrum.eval_target_sum
assert_compatible GUT.LeptonTrialitySpectrum.exists_joint_zeroMode => Physics.LeptonTrialitySpectrum.exists_joint_zeroMode
assert_compatible GUT.LeptonTrialitySpectrum.full_spectrum_eq => Physics.LeptonTrialitySpectrum.full_spectrum_eq
assert_compatible GUT.LeptonTrialitySpectrum.inclusion => Physics.LeptonTrialitySpectrum.inclusion
assert_compatible GUT.LeptonTrialitySpectrum.keyCharacter => Physics.LeptonTrialitySpectrum.keyCharacter
assert_compatible GUT.LeptonTrialitySpectrum.keyCharacter.eq_1 => Physics.LeptonTrialitySpectrum.keyCharacter.eq_1
assert_compatible GUT.LeptonTrialitySpectrum.keyCharacter_injective => Physics.LeptonTrialitySpectrum.keyCharacter_injective
assert_compatible GUT.LeptonTrialitySpectrum.lift => Physics.LeptonTrialitySpectrum.lift
assert_compatible GUT.LeptonTrialitySpectrum.lift.eq_1 => Physics.LeptonTrialitySpectrum.lift.eq_1
assert_compatible GUT.LeptonTrialitySpectrum.radical_dual_trace => Physics.LeptonTrialitySpectrum.radical_dual_trace
assert_compatible GUT.LeptonTrialitySpectrum.radical_trace => Physics.LeptonTrialitySpectrum.radical_trace
assert_compatible GUT.LeptonTrialitySpectrum.restricted => Physics.LeptonTrialitySpectrum.restricted
assert_compatible GUT.LeptonTrialitySpectrum.restrictedMass => Physics.LeptonTrialitySpectrum.restrictedMass
assert_compatible GUT.LeptonTrialitySpectrum.restrictedMass_eq_zero => Physics.LeptonTrialitySpectrum.restrictedMass_eq_zero
assert_compatible GUT.LeptonTrialitySpectrum.restricted_unitary => Physics.LeptonTrialitySpectrum.restricted_unitary
assert_compatible GUT.LeptonTrialitySpectrum.trace_target => Physics.LeptonTrialitySpectrum.trace_target
