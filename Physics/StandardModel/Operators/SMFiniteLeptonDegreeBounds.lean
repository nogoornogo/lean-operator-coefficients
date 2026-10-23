import Physics.StandardModel.Operators.Support.Dimension.SMFiniteLeptonDegreeBounds
import Physics.StandardModel.Operators.SMFiniteLeptonAssignments
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMFiniteLeptonDegreeBounds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFiniteLeptonDegreeBounds.allowed_application_count => Physics.SMFiniteLeptonDegreeBounds.allowed_application_count,
  GUT.SMFiniteLeptonDegreeBounds.b1_minimum_none_iff => Physics.SMFiniteLeptonDegreeBounds.b1_minimum_none_iff,
  GUT.SMFiniteLeptonDegreeBounds.b1_minimum_some_iff => Physics.SMFiniteLeptonDegreeBounds.b1_minimum_some_iff,
  GUT.SMFiniteLeptonDegreeBounds.b1_row_bounds => Physics.SMFiniteLeptonDegreeBounds.b1_row_bounds,
  GUT.SMFiniteLeptonDegreeBounds.b2_minimum_none_iff => Physics.SMFiniteLeptonDegreeBounds.b2_minimum_none_iff,
  GUT.SMFiniteLeptonDegreeBounds.b2_minimum_some_iff => Physics.SMFiniteLeptonDegreeBounds.b2_minimum_some_iff,
  GUT.SMFiniteLeptonDegreeBounds.b2_row_bounds => Physics.SMFiniteLeptonDegreeBounds.b2_row_bounds,
  GUT.SMFiniteLeptonDegreeBounds.highLepton => Physics.SMFiniteLeptonDegreeBounds.highLepton,
  GUT.SMFiniteLeptonDegreeBounds.highLeptonCount => Physics.SMFiniteLeptonDegreeBounds.highLeptonCount,
  GUT.SMFiniteLeptonDegreeBounds.high_degree_counts => Physics.SMFiniteLeptonDegreeBounds.high_degree_counts,
  GUT.SMFiniteLeptonDegreeBounds.high_row_bounds => Physics.SMFiniteLeptonDegreeBounds.high_row_bounds,
  GUT.SMFiniteLeptonDegreeBounds.leptonSizes => Physics.SMFiniteLeptonDegreeBounds.leptonSizes,
  GUT.SMFiniteLeptonDegreeBounds.leptonSizes.eq_1 => Physics.SMFiniteLeptonDegreeBounds.leptonSizes.eq_1,
  GUT.SMFiniteLeptonDegreeBounds.minLepton => Physics.SMFiniteLeptonDegreeBounds.minLepton,
  GUT.SMFiniteLeptonDegreeBounds.minLepton.eq_1 => Physics.SMFiniteLeptonDegreeBounds.minLepton.eq_1,
  GUT.SMFiniteLeptonDegreeBounds.min_exists_iff => Physics.SMFiniteLeptonDegreeBounds.min_exists_iff,
  GUT.SMFiniteLeptonDegreeBounds.min_none_forbidden => Physics.SMFiniteLeptonDegreeBounds.min_none_forbidden,
  GUT.SMFiniteLeptonDegreeBounds.min_none_iff => Physics.SMFiniteLeptonDegreeBounds.min_none_iff,
  GUT.SMFiniteLeptonDegreeBounds.min_some_spec => Physics.SMFiniteLeptonDegreeBounds.min_some_spec,
  GUT.SMFiniteLeptonDegreeBounds.minimumCount => Physics.SMFiniteLeptonDegreeBounds.minimumCount,
  GUT.SMFiniteLeptonDegreeBounds.minimum_attained => Physics.SMFiniteLeptonDegreeBounds.minimum_attained,
  GUT.SMFiniteLeptonDegreeBounds.minimum_distributions => Physics.SMFiniteLeptonDegreeBounds.minimum_distributions,
  GUT.SMFiniteLeptonDegreeBounds.minimum_le_eighteen => Physics.SMFiniteLeptonDegreeBounds.minimum_le_eighteen,
  GUT.SMFiniteLeptonDegreeBounds.neutralLeptons => Physics.SMFiniteLeptonDegreeBounds.neutralLeptons,
  GUT.SMFiniteLeptonDegreeBounds.neutralLeptons.eq_1 => Physics.SMFiniteLeptonDegreeBounds.neutralLeptons.eq_1,
  GUT.SMFiniteLeptonDegreeBounds.normalized_content => Physics.SMFiniteLeptonDegreeBounds.normalized_content,
  GUT.SMFiniteLeptonDegreeBounds.original_degree_lower => Physics.SMFiniteLeptonDegreeBounds.original_degree_lower,
  GUT.SMFiniteLeptonDegreeBounds.original_lepton_lower => Physics.SMFiniteLeptonDegreeBounds.original_lepton_lower,
  GUT.SMFiniteLeptonDegreeBounds.rowMinimum => Physics.SMFiniteLeptonDegreeBounds.rowMinimum,
  GUT.SMFiniteLeptonDegreeBounds.sizes_nonempty_iff => Physics.SMFiniteLeptonDegreeBounds.sizes_nonempty_iff
]

assert_compatible GUT.SMFiniteLeptonDegreeBounds.allowed_application_count => Physics.SMFiniteLeptonDegreeBounds.allowed_application_count
assert_compatible GUT.SMFiniteLeptonDegreeBounds.b1_minimum_none_iff => Physics.SMFiniteLeptonDegreeBounds.b1_minimum_none_iff
assert_compatible GUT.SMFiniteLeptonDegreeBounds.b1_minimum_some_iff => Physics.SMFiniteLeptonDegreeBounds.b1_minimum_some_iff
assert_compatible GUT.SMFiniteLeptonDegreeBounds.b1_row_bounds => Physics.SMFiniteLeptonDegreeBounds.b1_row_bounds
assert_compatible GUT.SMFiniteLeptonDegreeBounds.b2_minimum_none_iff => Physics.SMFiniteLeptonDegreeBounds.b2_minimum_none_iff
assert_compatible GUT.SMFiniteLeptonDegreeBounds.b2_minimum_some_iff => Physics.SMFiniteLeptonDegreeBounds.b2_minimum_some_iff
assert_compatible GUT.SMFiniteLeptonDegreeBounds.b2_row_bounds => Physics.SMFiniteLeptonDegreeBounds.b2_row_bounds
assert_compatible GUT.SMFiniteLeptonDegreeBounds.highLepton => Physics.SMFiniteLeptonDegreeBounds.highLepton
assert_compatible GUT.SMFiniteLeptonDegreeBounds.highLeptonCount => Physics.SMFiniteLeptonDegreeBounds.highLeptonCount
assert_compatible GUT.SMFiniteLeptonDegreeBounds.high_degree_counts => Physics.SMFiniteLeptonDegreeBounds.high_degree_counts
assert_compatible GUT.SMFiniteLeptonDegreeBounds.high_row_bounds => Physics.SMFiniteLeptonDegreeBounds.high_row_bounds
assert_compatible GUT.SMFiniteLeptonDegreeBounds.leptonSizes => Physics.SMFiniteLeptonDegreeBounds.leptonSizes
assert_compatible GUT.SMFiniteLeptonDegreeBounds.leptonSizes.eq_1 => Physics.SMFiniteLeptonDegreeBounds.leptonSizes.eq_1
assert_compatible GUT.SMFiniteLeptonDegreeBounds.minLepton => Physics.SMFiniteLeptonDegreeBounds.minLepton
assert_compatible GUT.SMFiniteLeptonDegreeBounds.minLepton.eq_1 => Physics.SMFiniteLeptonDegreeBounds.minLepton.eq_1
assert_compatible GUT.SMFiniteLeptonDegreeBounds.min_exists_iff => Physics.SMFiniteLeptonDegreeBounds.min_exists_iff
assert_compatible GUT.SMFiniteLeptonDegreeBounds.min_none_forbidden => Physics.SMFiniteLeptonDegreeBounds.min_none_forbidden
assert_compatible GUT.SMFiniteLeptonDegreeBounds.min_none_iff => Physics.SMFiniteLeptonDegreeBounds.min_none_iff
assert_compatible GUT.SMFiniteLeptonDegreeBounds.min_some_spec => Physics.SMFiniteLeptonDegreeBounds.min_some_spec
assert_compatible GUT.SMFiniteLeptonDegreeBounds.minimumCount => Physics.SMFiniteLeptonDegreeBounds.minimumCount
assert_compatible GUT.SMFiniteLeptonDegreeBounds.minimum_attained => Physics.SMFiniteLeptonDegreeBounds.minimum_attained
assert_compatible GUT.SMFiniteLeptonDegreeBounds.minimum_distributions => Physics.SMFiniteLeptonDegreeBounds.minimum_distributions
assert_compatible GUT.SMFiniteLeptonDegreeBounds.minimum_le_eighteen => Physics.SMFiniteLeptonDegreeBounds.minimum_le_eighteen
assert_compatible GUT.SMFiniteLeptonDegreeBounds.neutralLeptons => Physics.SMFiniteLeptonDegreeBounds.neutralLeptons
assert_compatible GUT.SMFiniteLeptonDegreeBounds.neutralLeptons.eq_1 => Physics.SMFiniteLeptonDegreeBounds.neutralLeptons.eq_1
assert_compatible GUT.SMFiniteLeptonDegreeBounds.normalized_content => Physics.SMFiniteLeptonDegreeBounds.normalized_content
assert_compatible GUT.SMFiniteLeptonDegreeBounds.original_degree_lower => Physics.SMFiniteLeptonDegreeBounds.original_degree_lower
assert_compatible GUT.SMFiniteLeptonDegreeBounds.original_lepton_lower => Physics.SMFiniteLeptonDegreeBounds.original_lepton_lower
assert_compatible GUT.SMFiniteLeptonDegreeBounds.rowMinimum => Physics.SMFiniteLeptonDegreeBounds.rowMinimum
assert_compatible GUT.SMFiniteLeptonDegreeBounds.sizes_nonempty_iff => Physics.SMFiniteLeptonDegreeBounds.sizes_nonempty_iff
