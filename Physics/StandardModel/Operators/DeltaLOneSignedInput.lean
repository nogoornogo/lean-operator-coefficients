import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedInput
import Physics.StandardModel.Operators.DeltaLOneSpeciesSupport
import Math.RepresentationTheory.FiniteSpeciesExterior
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaLOneSignedInput.Coefficient => Physics.DeltaLOneSignedInput.Coefficient,
  GUT.DeltaLOneSignedInput.Species => Physics.DeltaLOneSignedInput.Species,
  GUT.DeltaLOneSignedInput.baryon => Physics.DeltaLOneSignedInput.baryon,
  GUT.DeltaLOneSignedInput.baryon.eq_1 => Physics.DeltaLOneSignedInput.baryon.eq_1,
  GUT.DeltaLOneSignedInput.baryon_counts => Physics.DeltaLOneSignedInput.baryon_counts,
  GUT.DeltaLOneSignedInput.counts => Physics.DeltaLOneSignedInput.counts,
  GUT.DeltaLOneSignedInput.counts.eq_1 => Physics.DeltaLOneSignedInput.counts.eq_1,
  GUT.DeltaLOneSignedInput.gauge_candidates => Physics.DeltaLOneSignedInput.gauge_candidates,
  GUT.DeltaLOneSignedInput.hypercharge => Physics.DeltaLOneSignedInput.hypercharge,
  GUT.DeltaLOneSignedInput.hypercharge.eq_1 => Physics.DeltaLOneSignedInput.hypercharge.eq_1,
  GUT.DeltaLOneSignedInput.hypercharge_counts => Physics.DeltaLOneSignedInput.hypercharge_counts,
  GUT.DeltaLOneSignedInput.hypercharge_of_nonzero => Physics.DeltaLOneSignedInput.hypercharge_of_nonzero,
  GUT.DeltaLOneSignedInput.lepton => Physics.DeltaLOneSignedInput.lepton,
  GUT.DeltaLOneSignedInput.lepton.eq_1 => Physics.DeltaLOneSignedInput.lepton.eq_1,
  GUT.DeltaLOneSignedInput.lepton_counts => Physics.DeltaLOneSignedInput.lepton_counts,
  GUT.DeltaLOneSignedInput.lepton_of_nonzero => Physics.DeltaLOneSignedInput.lepton_of_nonzero,
  GUT.DeltaLOneSignedInput.multiplicity => Physics.DeltaLOneSignedInput.multiplicity,
  GUT.DeltaLOneSignedInput.multiplicity.eq_1 => Physics.DeltaLOneSignedInput.multiplicity.eq_1,
  GUT.DeltaLOneSignedInput.sector => Physics.DeltaLOneSignedInput.sector,
  GUT.DeltaLOneSignedInput.slotCount_counts => Physics.DeltaLOneSignedInput.slotCount_counts,
  GUT.DeltaLOneSignedInput.sum_weights => Physics.DeltaLOneSignedInput.sum_weights,
  GUT.DeltaLOneSignedInput.triality_of_nonzero => Physics.DeltaLOneSignedInput.triality_of_nonzero,
  GUT.DeltaLOneSignedInput.vanish_outside_gauge_candidates => Physics.DeltaLOneSignedInput.vanish_outside_gauge_candidates
]

assert_compatible GUT.DeltaLOneSignedInput.Coefficient => Physics.DeltaLOneSignedInput.Coefficient
assert_compatible GUT.DeltaLOneSignedInput.Species => Physics.DeltaLOneSignedInput.Species
assert_compatible GUT.DeltaLOneSignedInput.baryon => Physics.DeltaLOneSignedInput.baryon
assert_compatible GUT.DeltaLOneSignedInput.baryon.eq_1 => Physics.DeltaLOneSignedInput.baryon.eq_1
assert_compatible GUT.DeltaLOneSignedInput.baryon_counts => Physics.DeltaLOneSignedInput.baryon_counts
assert_compatible GUT.DeltaLOneSignedInput.counts => Physics.DeltaLOneSignedInput.counts
assert_compatible GUT.DeltaLOneSignedInput.counts.eq_1 => Physics.DeltaLOneSignedInput.counts.eq_1
assert_compatible GUT.DeltaLOneSignedInput.gauge_candidates => Physics.DeltaLOneSignedInput.gauge_candidates
assert_compatible GUT.DeltaLOneSignedInput.hypercharge => Physics.DeltaLOneSignedInput.hypercharge
assert_compatible GUT.DeltaLOneSignedInput.hypercharge.eq_1 => Physics.DeltaLOneSignedInput.hypercharge.eq_1
assert_compatible GUT.DeltaLOneSignedInput.hypercharge_counts => Physics.DeltaLOneSignedInput.hypercharge_counts
assert_compatible GUT.DeltaLOneSignedInput.hypercharge_of_nonzero => Physics.DeltaLOneSignedInput.hypercharge_of_nonzero
assert_compatible GUT.DeltaLOneSignedInput.lepton => Physics.DeltaLOneSignedInput.lepton
assert_compatible GUT.DeltaLOneSignedInput.lepton.eq_1 => Physics.DeltaLOneSignedInput.lepton.eq_1
assert_compatible GUT.DeltaLOneSignedInput.lepton_counts => Physics.DeltaLOneSignedInput.lepton_counts
assert_compatible GUT.DeltaLOneSignedInput.lepton_of_nonzero => Physics.DeltaLOneSignedInput.lepton_of_nonzero
assert_compatible GUT.DeltaLOneSignedInput.multiplicity => Physics.DeltaLOneSignedInput.multiplicity
assert_compatible GUT.DeltaLOneSignedInput.multiplicity.eq_1 => Physics.DeltaLOneSignedInput.multiplicity.eq_1
assert_compatible GUT.DeltaLOneSignedInput.sector => Physics.DeltaLOneSignedInput.sector
assert_compatible GUT.DeltaLOneSignedInput.slotCount_counts => Physics.DeltaLOneSignedInput.slotCount_counts
assert_compatible GUT.DeltaLOneSignedInput.sum_weights => Physics.DeltaLOneSignedInput.sum_weights
assert_compatible GUT.DeltaLOneSignedInput.triality_of_nonzero => Physics.DeltaLOneSignedInput.triality_of_nonzero
assert_compatible GUT.DeltaLOneSignedInput.vanish_outside_gauge_candidates => Physics.DeltaLOneSignedInput.vanish_outside_gauge_candidates
