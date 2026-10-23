import Physics.StandardModel.Spectrum.Representations.SMPartialTarget
import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.SMPartialTarget instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMPartialTarget.MatchesSM => Physics.SMPartialTarget.MatchesSM,
  GUT.SMPartialTarget.add_of_dual_vanishes => Physics.SMPartialTarget.add_of_dual_vanishes,
  GUT.SMPartialTarget.chargesSupported_of_occupied => Physics.SMPartialTarget.chargesSupported_of_occupied,
  GUT.SMPartialTarget.coefficient_lower_bound => Physics.SMPartialTarget.coefficient_lower_bound,
  GUT.SMPartialTarget.of_full_target => Physics.SMPartialTarget.of_full_target,
  GUT.SMPartialTarget.profile_eq => Physics.SMPartialTarget.profile_eq
]

assert_compatible GUT.SMPartialTarget.MatchesSM => Physics.SMPartialTarget.MatchesSM
assert_compatible GUT.SMPartialTarget.add_of_dual_vanishes => Physics.SMPartialTarget.add_of_dual_vanishes
assert_compatible GUT.SMPartialTarget.chargesSupported_of_occupied => Physics.SMPartialTarget.chargesSupported_of_occupied
assert_compatible GUT.SMPartialTarget.coefficient_lower_bound => Physics.SMPartialTarget.coefficient_lower_bound
assert_compatible GUT.SMPartialTarget.of_full_target => Physics.SMPartialTarget.of_full_target
assert_compatible GUT.SMPartialTarget.profile_eq => Physics.SMPartialTarget.profile_eq
