import Physics.StandardModel.Operators.Support.Coordinates.SMSparseSupport
import Physics.StandardModel.Operators.SMSparseCharacter
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMSparseSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMSparseQLSupport.original_allowed_iff => Physics.SMSparseQLSupport.original_allowed_iff,
  GUT.SMSparseQLSupport.test => Physics.SMSparseQLSupport.test,
  GUT.SMSparseQLSupport.test.eq_1 => Physics.SMSparseQLSupport.test.eq_1,
  GUT.SMSparseQLSupport.test_allowed_iff => Physics.SMSparseQLSupport.test_allowed_iff,
  GUT.SMSparseQLSupport.test_reference => Physics.SMSparseQLSupport.test_reference,
  GUT.SMSparseSupport.kernel_dimension => Physics.SMSparseSupport.kernel_dimension,
  GUT.SMSparseSupport.kernel_dimension_int => Physics.SMSparseSupport.kernel_dimension_int,
  GUT.SMSparseSupport.local_allowed_iff => Physics.SMSparseSupport.local_allowed_iff,
  GUT.SMSparseSupport.rank_formula => Physics.SMSparseSupport.rank_formula
]

assert_compatible GUT.SMSparseQLSupport.original_allowed_iff => Physics.SMSparseQLSupport.original_allowed_iff
assert_compatible GUT.SMSparseQLSupport.test => Physics.SMSparseQLSupport.test
assert_compatible GUT.SMSparseQLSupport.test.eq_1 => Physics.SMSparseQLSupport.test.eq_1
assert_compatible GUT.SMSparseQLSupport.test_allowed_iff => Physics.SMSparseQLSupport.test_allowed_iff
assert_compatible GUT.SMSparseQLSupport.test_reference => Physics.SMSparseQLSupport.test_reference
assert_compatible GUT.SMSparseSupport.kernel_dimension => Physics.SMSparseSupport.kernel_dimension
assert_compatible GUT.SMSparseSupport.kernel_dimension_int => Physics.SMSparseSupport.kernel_dimension_int
assert_compatible GUT.SMSparseSupport.local_allowed_iff => Physics.SMSparseSupport.local_allowed_iff
assert_compatible GUT.SMSparseSupport.rank_formula => Physics.SMSparseSupport.rank_formula
