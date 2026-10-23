import Physics.StandardModel.Operators.Support.Dimension.SMB1MinimumClassification
import Physics.StandardModel.Operators.SMB1DimensionWitnesses
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1MinimumClassification instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1MinimumClassification.cutoffLower => Physics.SMB1MinimumClassification.cutoffLower,
  GUT.SMB1MinimumClassification.cutoff_lower => Physics.SMB1MinimumClassification.cutoff_lower,
  GUT.SMB1MinimumClassification.exactCheck => Physics.SMB1MinimumClassification.exactCheck,
  GUT.SMB1MinimumClassification.exactCheck.eq_1 => Physics.SMB1MinimumClassification.exactCheck.eq_1,
  GUT.SMB1MinimumClassification.exactCount => Physics.SMB1MinimumClassification.exactCount,
  GUT.SMB1MinimumClassification.exact_check_semantics => Physics.SMB1MinimumClassification.exact_check_semantics,
  GUT.SMB1MinimumClassification.exact_of_match => Physics.SMB1MinimumClassification.exact_of_match,
  GUT.SMB1MinimumClassification.intervalCheck => Physics.SMB1MinimumClassification.intervalCheck,
  GUT.SMB1MinimumClassification.intervalCheck.eq_1 => Physics.SMB1MinimumClassification.intervalCheck.eq_1,
  GUT.SMB1MinimumClassification.interval_counts => Physics.SMB1MinimumClassification.interval_counts,
  GUT.SMB1MinimumClassification.minimum => Physics.SMB1MinimumClassification.minimum,
  GUT.SMB1MinimumClassification.minimum.eq_1 => Physics.SMB1MinimumClassification.minimum.eq_1,
  GUT.SMB1MinimumClassification.minimum_none_iff => Physics.SMB1MinimumClassification.minimum_none_iff,
  GUT.SMB1MinimumClassification.minimum_some_spec => Physics.SMB1MinimumClassification.minimum_some_spec,
  GUT.SMB1MinimumClassification.numeric_inventory => Physics.SMB1MinimumClassification.numeric_inventory,
  GUT.SMB1MinimumClassification.rowLower => Physics.SMB1MinimumClassification.rowLower,
  GUT.SMB1MinimumClassification.rowUpper => Physics.SMB1MinimumClassification.rowUpper,
  GUT.SMB1MinimumClassification.row_certificate => Physics.SMB1MinimumClassification.row_certificate,
  GUT.SMB1MinimumClassification.row_exact => Physics.SMB1MinimumClassification.row_exact,
  GUT.SMB1MinimumClassification.row_intervals => Physics.SMB1MinimumClassification.row_intervals,
  GUT.SMB1MinimumClassification.row_lower_bound => Physics.SMB1MinimumClassification.row_lower_bound,
  GUT.SMB1MinimumClassification.universal_lower => Physics.SMB1MinimumClassification.universal_lower,
  GUT.SMB1MinimumClassification.unresolvedCount => Physics.SMB1MinimumClassification.unresolvedCount,
  GUT.SMB1MinimumClassification.upper_attainment => Physics.SMB1MinimumClassification.upper_attainment,
  GUT.SMB1MinimumClassification.values => Physics.SMB1MinimumClassification.values,
  GUT.SMB1MinimumClassification.values.eq_1 => Physics.SMB1MinimumClassification.values.eq_1
]

assert_compatible GUT.SMB1MinimumClassification.cutoffLower => Physics.SMB1MinimumClassification.cutoffLower
assert_compatible GUT.SMB1MinimumClassification.cutoff_lower => Physics.SMB1MinimumClassification.cutoff_lower
assert_compatible GUT.SMB1MinimumClassification.exactCheck => Physics.SMB1MinimumClassification.exactCheck
assert_compatible GUT.SMB1MinimumClassification.exactCheck.eq_1 => Physics.SMB1MinimumClassification.exactCheck.eq_1
assert_compatible GUT.SMB1MinimumClassification.exactCount => Physics.SMB1MinimumClassification.exactCount
assert_compatible GUT.SMB1MinimumClassification.exact_check_semantics => Physics.SMB1MinimumClassification.exact_check_semantics
assert_compatible GUT.SMB1MinimumClassification.exact_of_match => Physics.SMB1MinimumClassification.exact_of_match
assert_compatible GUT.SMB1MinimumClassification.intervalCheck => Physics.SMB1MinimumClassification.intervalCheck
assert_compatible GUT.SMB1MinimumClassification.intervalCheck.eq_1 => Physics.SMB1MinimumClassification.intervalCheck.eq_1
assert_compatible GUT.SMB1MinimumClassification.interval_counts => Physics.SMB1MinimumClassification.interval_counts
assert_compatible GUT.SMB1MinimumClassification.minimum => Physics.SMB1MinimumClassification.minimum
assert_compatible GUT.SMB1MinimumClassification.minimum.eq_1 => Physics.SMB1MinimumClassification.minimum.eq_1
assert_compatible GUT.SMB1MinimumClassification.minimum_none_iff => Physics.SMB1MinimumClassification.minimum_none_iff
assert_compatible GUT.SMB1MinimumClassification.minimum_some_spec => Physics.SMB1MinimumClassification.minimum_some_spec
assert_compatible GUT.SMB1MinimumClassification.numeric_inventory => Physics.SMB1MinimumClassification.numeric_inventory
assert_compatible GUT.SMB1MinimumClassification.rowLower => Physics.SMB1MinimumClassification.rowLower
assert_compatible GUT.SMB1MinimumClassification.rowUpper => Physics.SMB1MinimumClassification.rowUpper
assert_compatible GUT.SMB1MinimumClassification.row_certificate => Physics.SMB1MinimumClassification.row_certificate
assert_compatible GUT.SMB1MinimumClassification.row_exact => Physics.SMB1MinimumClassification.row_exact
assert_compatible GUT.SMB1MinimumClassification.row_intervals => Physics.SMB1MinimumClassification.row_intervals
assert_compatible GUT.SMB1MinimumClassification.row_lower_bound => Physics.SMB1MinimumClassification.row_lower_bound
assert_compatible GUT.SMB1MinimumClassification.universal_lower => Physics.SMB1MinimumClassification.universal_lower
assert_compatible GUT.SMB1MinimumClassification.unresolvedCount => Physics.SMB1MinimumClassification.unresolvedCount
assert_compatible GUT.SMB1MinimumClassification.upper_attainment => Physics.SMB1MinimumClassification.upper_attainment
assert_compatible GUT.SMB1MinimumClassification.values => Physics.SMB1MinimumClassification.values
assert_compatible GUT.SMB1MinimumClassification.values.eq_1 => Physics.SMB1MinimumClassification.values.eq_1
