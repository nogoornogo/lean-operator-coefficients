import Physics.StandardModel.Spectrum.Representations.QqueLocalTarget
import Physics.StandardModel.Spectrum.SMPartialTarget
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.QqueLocalTarget instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueLocalTarget.Matches => Physics.QqueLocalTarget.Matches,
  GUT.QqueLocalTarget.Monitored => Physics.QqueLocalTarget.Monitored,
  GUT.QqueLocalTarget.add_of_dual_vanishes => Physics.QqueLocalTarget.add_of_dual_vanishes,
  GUT.QqueLocalTarget.coefficient_lower_bound => Physics.QqueLocalTarget.coefficient_lower_bound,
  GUT.QqueLocalTarget.matches_iff_of_profiles_eq => Physics.QqueLocalTarget.matches_iff_of_profiles_eq,
  GUT.QqueLocalTarget.of_matchesSM => Physics.QqueLocalTarget.of_matchesSM,
  GUT.QqueLocalTarget.profile_eq => Physics.QqueLocalTarget.profile_eq
]

assert_compatible GUT.QqueLocalTarget.Matches => Physics.QqueLocalTarget.Matches
assert_compatible GUT.QqueLocalTarget.Monitored => Physics.QqueLocalTarget.Monitored
assert_compatible GUT.QqueLocalTarget.add_of_dual_vanishes => Physics.QqueLocalTarget.add_of_dual_vanishes
assert_compatible GUT.QqueLocalTarget.coefficient_lower_bound => Physics.QqueLocalTarget.coefficient_lower_bound
assert_compatible GUT.QqueLocalTarget.matches_iff_of_profiles_eq => Physics.QqueLocalTarget.matches_iff_of_profiles_eq
assert_compatible GUT.QqueLocalTarget.of_matchesSM => Physics.QqueLocalTarget.of_matchesSM
assert_compatible GUT.QqueLocalTarget.profile_eq => Physics.QqueLocalTarget.profile_eq
