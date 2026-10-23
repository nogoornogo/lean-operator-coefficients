import Physics.StandardModel.Operators.Support.Joint.SMMixedWeakCapacity
import Math.RepresentationTheory.ContentTorusBound
import Physics.StandardModel.Operators.SMConstantWeakCapacity
import Physics.StandardModel.Operators.SMIteratedContent
import Physics.StandardModel.Operators.SMLowerHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedWeakCapacity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMMixedWeakCapacity.bound => Physics.SMMixedWeakCapacity.bound,
  GUT.SMMixedWeakCapacity.exterior_bounded => Physics.SMMixedWeakCapacity.exterior_bounded,
  GUT.SMMixedWeakCapacity.local_high_forbidden => Physics.SMMixedWeakCapacity.local_high_forbidden,
  GUT.SMMixedWeakCapacity.local_high_zero => Physics.SMMixedWeakCapacity.local_high_zero,
  GUT.SMMixedWeakCapacity.original_ql_forbidden => Physics.SMMixedWeakCapacity.original_ql_forbidden,
  GUT.SMMixedWeakCapacity.saturated_bound_zero => Physics.SMMixedWeakCapacity.saturated_bound_zero,
  GUT.SMMixedWeakCapacity.saturated_original_ql_forbidden => Physics.SMMixedWeakCapacity.saturated_original_ql_forbidden,
  GUT.SMMixedWeakCapacity.source_bounded => Physics.SMMixedWeakCapacity.source_bounded,
  GUT.SMMixedWeakCapacity.speciesBound => Physics.SMMixedWeakCapacity.speciesBound
]

assert_compatible GUT.SMMixedWeakCapacity.bound => Physics.SMMixedWeakCapacity.bound
assert_compatible GUT.SMMixedWeakCapacity.exterior_bounded => Physics.SMMixedWeakCapacity.exterior_bounded
assert_compatible GUT.SMMixedWeakCapacity.local_high_forbidden => Physics.SMMixedWeakCapacity.local_high_forbidden
assert_compatible GUT.SMMixedWeakCapacity.local_high_zero => Physics.SMMixedWeakCapacity.local_high_zero
assert_compatible GUT.SMMixedWeakCapacity.original_ql_forbidden => Physics.SMMixedWeakCapacity.original_ql_forbidden
assert_compatible GUT.SMMixedWeakCapacity.saturated_bound_zero => Physics.SMMixedWeakCapacity.saturated_bound_zero
assert_compatible GUT.SMMixedWeakCapacity.saturated_original_ql_forbidden => Physics.SMMixedWeakCapacity.saturated_original_ql_forbidden
assert_compatible GUT.SMMixedWeakCapacity.source_bounded => Physics.SMMixedWeakCapacity.source_bounded
assert_compatible GUT.SMMixedWeakCapacity.speciesBound => Physics.SMMixedWeakCapacity.speciesBound
