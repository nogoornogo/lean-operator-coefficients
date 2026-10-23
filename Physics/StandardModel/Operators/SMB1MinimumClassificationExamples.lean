import Physics.StandardModel.Operators.Support.Dimension.SMB1MinimumClassificationExamples
import Physics.StandardModel.Operators.SMB1MinimumClassification
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1MinimumClassificationExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1MinimumClassificationExamples.all_row_consumer => Physics.SMB1MinimumClassificationExamples.all_row_consumer,
  GUT.SMB1MinimumClassificationExamples.k11_actual_upper => Physics.SMB1MinimumClassificationExamples.k11_actual_upper,
  GUT.SMB1MinimumClassificationExamples.k11_gap => Physics.SMB1MinimumClassificationExamples.k11_gap,
  GUT.SMB1MinimumClassificationExamples.k3_exact => Physics.SMB1MinimumClassificationExamples.k3_exact,
  GUT.SMB1MinimumClassificationExamples.k5_exact => Physics.SMB1MinimumClassificationExamples.k5_exact,
  GUT.SMB1MinimumClassificationExamples.k5_gap => Physics.SMB1MinimumClassificationExamples.k5_gap
]

assert_compatible GUT.SMB1MinimumClassificationExamples.all_row_consumer => Physics.SMB1MinimumClassificationExamples.all_row_consumer
assert_compatible GUT.SMB1MinimumClassificationExamples.k11_actual_upper => Physics.SMB1MinimumClassificationExamples.k11_actual_upper
assert_compatible GUT.SMB1MinimumClassificationExamples.k11_gap => Physics.SMB1MinimumClassificationExamples.k11_gap
assert_compatible GUT.SMB1MinimumClassificationExamples.k3_exact => Physics.SMB1MinimumClassificationExamples.k3_exact
assert_compatible GUT.SMB1MinimumClassificationExamples.k5_exact => Physics.SMB1MinimumClassificationExamples.k5_exact
assert_compatible GUT.SMB1MinimumClassificationExamples.k5_gap => Physics.SMB1MinimumClassificationExamples.k5_gap
