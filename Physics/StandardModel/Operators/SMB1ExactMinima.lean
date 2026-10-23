import Physics.StandardModel.Operators.Support.Dimension.SMB1ExactMinima
import Physics.StandardModel.Operators.SMB1StrongDimensionBounds
import Physics.StandardModel.Operators.SMB1MinimumClassification
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1ExactMinima instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1ExactMinima.classified_count => Physics.SMB1ExactMinima.classified_count,
  GUT.SMB1ExactMinima.exact_of_match => Physics.SMB1ExactMinima.exact_of_match,
  GUT.SMB1ExactMinima.lowerMinimum => Physics.SMB1ExactMinima.lowerMinimum,
  GUT.SMB1ExactMinima.minimumCount => Physics.SMB1ExactMinima.minimumCount,
  GUT.SMB1ExactMinima.minimum_distribution => Physics.SMB1ExactMinima.minimum_distribution,
  GUT.SMB1ExactMinima.none_iff_forbidden => Physics.SMB1ExactMinima.none_iff_forbidden,
  GUT.SMB1ExactMinima.numeric_match => Physics.SMB1ExactMinima.numeric_match,
  GUT.SMB1ExactMinima.rowMinimum => Physics.SMB1ExactMinima.rowMinimum,
  GUT.SMB1ExactMinima.row_forbidden_below => Physics.SMB1ExactMinima.row_forbidden_below,
  GUT.SMB1ExactMinima.row_match => Physics.SMB1ExactMinima.row_match,
  GUT.SMB1ExactMinima.row_minimum => Physics.SMB1ExactMinima.row_minimum,
  GUT.SMB1ExactMinima.row_none_iff => Physics.SMB1ExactMinima.row_none_iff,
  GUT.SMB1ExactMinima.universal_lower => Physics.SMB1ExactMinima.universal_lower
]

assert_compatible GUT.SMB1ExactMinima.classified_count => Physics.SMB1ExactMinima.classified_count
assert_compatible GUT.SMB1ExactMinima.exact_of_match => Physics.SMB1ExactMinima.exact_of_match
assert_compatible GUT.SMB1ExactMinima.lowerMinimum => Physics.SMB1ExactMinima.lowerMinimum
assert_compatible GUT.SMB1ExactMinima.minimumCount => Physics.SMB1ExactMinima.minimumCount
assert_compatible GUT.SMB1ExactMinima.minimum_distribution => Physics.SMB1ExactMinima.minimum_distribution
assert_compatible GUT.SMB1ExactMinima.none_iff_forbidden => Physics.SMB1ExactMinima.none_iff_forbidden
assert_compatible GUT.SMB1ExactMinima.numeric_match => Physics.SMB1ExactMinima.numeric_match
assert_compatible GUT.SMB1ExactMinima.rowMinimum => Physics.SMB1ExactMinima.rowMinimum
assert_compatible GUT.SMB1ExactMinima.row_forbidden_below => Physics.SMB1ExactMinima.row_forbidden_below
assert_compatible GUT.SMB1ExactMinima.row_match => Physics.SMB1ExactMinima.row_match
assert_compatible GUT.SMB1ExactMinima.row_minimum => Physics.SMB1ExactMinima.row_minimum
assert_compatible GUT.SMB1ExactMinima.row_none_iff => Physics.SMB1ExactMinima.row_none_iff
assert_compatible GUT.SMB1ExactMinima.universal_lower => Physics.SMB1ExactMinima.universal_lower
