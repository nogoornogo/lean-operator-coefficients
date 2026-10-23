import Physics.StandardModel.Operators.Support.Dimension.SMB1ExactMinimaExamples
import Physics.StandardModel.Operators.SMB1ExactMinima
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Dimension.SMB1ExactMinimaExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMB1ExactMinimaExamples.generic_row_minimum => Physics.SMB1ExactMinimaExamples.generic_row_minimum,
  GUT.SMB1ExactMinimaExamples.generic_weak_bound => Physics.SMB1ExactMinimaExamples.generic_weak_bound,
  GUT.SMB1ExactMinimaExamples.k11_minimum_thirty_one => Physics.SMB1ExactMinimaExamples.k11_minimum_thirty_one,
  GUT.SMB1ExactMinimaExamples.k2_all_degree_forbidden => Physics.SMB1ExactMinimaExamples.k2_all_degree_forbidden,
  GUT.SMB1ExactMinimaExamples.k2_none => Physics.SMB1ExactMinimaExamples.k2_none,
  GUT.SMB1ExactMinimaExamples.k5_minimum_seven => Physics.SMB1ExactMinimaExamples.k5_minimum_seven,
  GUT.SMB1ExactMinimaExamples.negative_baryon_below_minimum => Physics.SMB1ExactMinimaExamples.negative_baryon_below_minimum
]

assert_compatible GUT.SMB1ExactMinimaExamples.generic_row_minimum => Physics.SMB1ExactMinimaExamples.generic_row_minimum
assert_compatible GUT.SMB1ExactMinimaExamples.generic_weak_bound => Physics.SMB1ExactMinimaExamples.generic_weak_bound
assert_compatible GUT.SMB1ExactMinimaExamples.k11_minimum_thirty_one => Physics.SMB1ExactMinimaExamples.k11_minimum_thirty_one
assert_compatible GUT.SMB1ExactMinimaExamples.k2_all_degree_forbidden => Physics.SMB1ExactMinimaExamples.k2_all_degree_forbidden
assert_compatible GUT.SMB1ExactMinimaExamples.k2_none => Physics.SMB1ExactMinimaExamples.k2_none
assert_compatible GUT.SMB1ExactMinimaExamples.k5_minimum_seven => Physics.SMB1ExactMinimaExamples.k5_minimum_seven
assert_compatible GUT.SMB1ExactMinimaExamples.negative_baryon_below_minimum => Physics.SMB1ExactMinimaExamples.negative_baryon_below_minimum
