import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFullSeed
import Physics.StandardModel.Operators.OutsideFamilyHiggsTrials
import Physics.StandardModel.Operators.SixQuarkTwoCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFullSeed instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavoredCyclicSelection.flavor.eq_1 => Physics.FlavoredCyclicSelection.flavor.eq_1,
  GUT.SixQuarkFullSeed.Fields => Physics.SixQuarkFullSeed.Fields,
  GUT.SixQuarkFullSeed.all_forbidden_iff => Physics.SixQuarkFullSeed.all_forbidden_iff,
  GUT.SixQuarkFullSeed.allowed_iff => Physics.SixQuarkFullSeed.allowed_iff,
  GUT.SixQuarkFullSeed.forbidden_iff => Physics.SixQuarkFullSeed.forbidden_iff,
  GUT.SixQuarkFullSeed.inclusion => Physics.SixQuarkFullSeed.inclusion,
  GUT.SixQuarkFullSeed.inclusion.eq_1 => Physics.SixQuarkFullSeed.inclusion.eq_1,
  GUT.SixQuarkFullSeed.localSeed => Physics.SixQuarkFullSeed.localSeed,
  GUT.SixQuarkFullSeed.localSeed.eq_1 => Physics.SixQuarkFullSeed.localSeed.eq_1,
  GUT.SixQuarkFullSeed.localSeed_nonzero => Physics.SixQuarkFullSeed.localSeed_nonzero,
  GUT.SixQuarkFullSeed.phase_six => Physics.SixQuarkFullSeed.phase_six,
  GUT.SixQuarkFullSeed.projection => Physics.SixQuarkFullSeed.projection,
  GUT.SixQuarkFullSeed.projection.eq_1 => Physics.SixQuarkFullSeed.projection.eq_1,
  GUT.SixQuarkFullSeed.projection_action => Physics.SixQuarkFullSeed.projection_action,
  GUT.SixQuarkFullSeed.projection_inclusion => Physics.SixQuarkFullSeed.projection_inclusion,
  GUT.SixQuarkFullSeed.projection_single_zero => Physics.SixQuarkFullSeed.projection_single_zero,
  GUT.SixQuarkFullSeed.raw => Physics.SixQuarkFullSeed.raw,
  GUT.SixQuarkFullSeed.raw.eq_1 => Physics.SixQuarkFullSeed.raw.eq_1,
  GUT.SixQuarkFullSeed.raw_nonzero => Physics.SixQuarkFullSeed.raw_nonzero,
  GUT.SixQuarkFullSeed.seed => Physics.SixQuarkFullSeed.seed,
  GUT.SixQuarkFullSeed.seed_exists => Physics.SixQuarkFullSeed.seed_exists,
  GUT.SixQuarkFullSeed.seed_nonzero => Physics.SixQuarkFullSeed.seed_nonzero,
  GUT.SixQuarkFullSeed.strip => Physics.SixQuarkFullSeed.strip,
  GUT.SixQuarkFullSeed.strip.eq_1 => Physics.SixQuarkFullSeed.strip.eq_1,
  GUT.SixQuarkFullSeed.strip_down_action => Physics.SixQuarkFullSeed.strip_down_action,
  GUT.SixQuarkFullSeed.strip_tmul => Physics.SixQuarkFullSeed.strip_tmul,
  GUT.SixQuarkFullSeed.strip_up_action => Physics.SixQuarkFullSeed.strip_up_action,
  GUT.SixQuarkFullSeed.support_of_nonzero => Physics.SixQuarkFullSeed.support_of_nonzero
]

assert_compatible GUT.FlavoredCyclicSelection.flavor.eq_1 => Physics.FlavoredCyclicSelection.flavor.eq_1
assert_compatible GUT.SixQuarkFullSeed.Fields => Physics.SixQuarkFullSeed.Fields
assert_compatible GUT.SixQuarkFullSeed.all_forbidden_iff => Physics.SixQuarkFullSeed.all_forbidden_iff
assert_compatible GUT.SixQuarkFullSeed.allowed_iff => Physics.SixQuarkFullSeed.allowed_iff
assert_compatible GUT.SixQuarkFullSeed.forbidden_iff => Physics.SixQuarkFullSeed.forbidden_iff
assert_compatible GUT.SixQuarkFullSeed.inclusion => Physics.SixQuarkFullSeed.inclusion
assert_compatible GUT.SixQuarkFullSeed.inclusion.eq_1 => Physics.SixQuarkFullSeed.inclusion.eq_1
assert_compatible GUT.SixQuarkFullSeed.localSeed => Physics.SixQuarkFullSeed.localSeed
assert_compatible GUT.SixQuarkFullSeed.localSeed.eq_1 => Physics.SixQuarkFullSeed.localSeed.eq_1
assert_compatible GUT.SixQuarkFullSeed.localSeed_nonzero => Physics.SixQuarkFullSeed.localSeed_nonzero
assert_compatible GUT.SixQuarkFullSeed.phase_six => Physics.SixQuarkFullSeed.phase_six
assert_compatible GUT.SixQuarkFullSeed.projection => Physics.SixQuarkFullSeed.projection
assert_compatible GUT.SixQuarkFullSeed.projection.eq_1 => Physics.SixQuarkFullSeed.projection.eq_1
assert_compatible GUT.SixQuarkFullSeed.projection_action => Physics.SixQuarkFullSeed.projection_action
assert_compatible GUT.SixQuarkFullSeed.projection_inclusion => Physics.SixQuarkFullSeed.projection_inclusion
assert_compatible GUT.SixQuarkFullSeed.projection_single_zero => Physics.SixQuarkFullSeed.projection_single_zero
assert_compatible GUT.SixQuarkFullSeed.raw => Physics.SixQuarkFullSeed.raw
assert_compatible GUT.SixQuarkFullSeed.raw.eq_1 => Physics.SixQuarkFullSeed.raw.eq_1
assert_compatible GUT.SixQuarkFullSeed.raw_nonzero => Physics.SixQuarkFullSeed.raw_nonzero
assert_compatible GUT.SixQuarkFullSeed.seed => Physics.SixQuarkFullSeed.seed
assert_compatible GUT.SixQuarkFullSeed.seed_exists => Physics.SixQuarkFullSeed.seed_exists
assert_compatible GUT.SixQuarkFullSeed.seed_nonzero => Physics.SixQuarkFullSeed.seed_nonzero
assert_compatible GUT.SixQuarkFullSeed.strip => Physics.SixQuarkFullSeed.strip
assert_compatible GUT.SixQuarkFullSeed.strip.eq_1 => Physics.SixQuarkFullSeed.strip.eq_1
assert_compatible GUT.SixQuarkFullSeed.strip_down_action => Physics.SixQuarkFullSeed.strip_down_action
assert_compatible GUT.SixQuarkFullSeed.strip_tmul => Physics.SixQuarkFullSeed.strip_tmul
assert_compatible GUT.SixQuarkFullSeed.strip_up_action => Physics.SixQuarkFullSeed.strip_up_action
assert_compatible GUT.SixQuarkFullSeed.support_of_nonzero => Physics.SixQuarkFullSeed.support_of_nonzero
