import Physics.StandardModel.Operators.Support.Coordinates.SMSaturatedContentSupport
import Physics.StandardModel.Operators.SMMixedWeakCapacity
import Physics.StandardModel.Operators.SMCompactLineSupport
import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMSaturatedContentSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMSaturatedContentSupport.Saturated => Physics.SMSaturatedContentSupport.Saturated,
  GUT.SMSaturatedContentSupport.model_zero_dimension => Physics.SMSaturatedContentSupport.model_zero_dimension,
  GUT.SMSaturatedContentSupport.neutral_local_allowed => Physics.SMSaturatedContentSupport.neutral_local_allowed,
  GUT.SMSaturatedContentSupport.original_ql_forbidden => Physics.SMSaturatedContentSupport.original_ql_forbidden,
  GUT.SMSaturatedContentSupport.original_ql_iff => Physics.SMSaturatedContentSupport.original_ql_iff,
  GUT.SMSaturatedContentSupport.source_dimension => Physics.SMSaturatedContentSupport.source_dimension
]

assert_compatible GUT.SMSaturatedContentSupport.Saturated => Physics.SMSaturatedContentSupport.Saturated
assert_compatible GUT.SMSaturatedContentSupport.model_zero_dimension => Physics.SMSaturatedContentSupport.model_zero_dimension
assert_compatible GUT.SMSaturatedContentSupport.neutral_local_allowed => Physics.SMSaturatedContentSupport.neutral_local_allowed
assert_compatible GUT.SMSaturatedContentSupport.original_ql_forbidden => Physics.SMSaturatedContentSupport.original_ql_forbidden
assert_compatible GUT.SMSaturatedContentSupport.original_ql_iff => Physics.SMSaturatedContentSupport.original_ql_iff
assert_compatible GUT.SMSaturatedContentSupport.source_dimension => Physics.SMSaturatedContentSupport.source_dimension
