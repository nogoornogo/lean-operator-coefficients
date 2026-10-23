import Physics.StandardModel.Operators.Support.Decomposition.SMComputableSupport
import Physics.StandardModel.Operators.SMComputableCharacter
import Physics.StandardModel.Operators.SMQLPatternRequests
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMComputableSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMComputableQLSupport.Conditions => Physics.SMComputableQLSupport.Conditions,
  GUT.SMComputableQLSupport.EntryAllowed => Physics.SMComputableQLSupport.EntryAllowed,
  GUT.SMComputableQLSupport.Input => Physics.SMComputableQLSupport.Input,
  GUT.SMComputableQLSupport.allowed_iff => Physics.SMComputableQLSupport.allowed_iff,
  GUT.SMComputableQLSupport.entry_allowed_iff => Physics.SMComputableQLSupport.entry_allowed_iff,
  GUT.SMComputableQLSupport.forbidden_iff => Physics.SMComputableQLSupport.forbidden_iff,
  GUT.SMComputableQLSupport.original_allowed_iff => Physics.SMComputableQLSupport.original_allowed_iff,
  GUT.SMComputableQLSupport.original_forbidden_iff => Physics.SMComputableQLSupport.original_forbidden_iff,
  GUT.SMComputableQLSupport.satisfies_iff => Physics.SMComputableQLSupport.satisfies_iff,
  GUT.SMComputableQLSupport.test => Physics.SMComputableQLSupport.test,
  GUT.SMComputableQLSupport.test.eq_1 => Physics.SMComputableQLSupport.test.eq_1,
  GUT.SMComputableQLSupport.test_allowed_iff => Physics.SMComputableQLSupport.test_allowed_iff,
  GUT.SMComputableSupport.compactBorel => Physics.SMComputableSupport.compactBorel,
  GUT.SMComputableSupport.compactMeasurable => Physics.SMComputableSupport.compactMeasurable,
  GUT.SMComputableSupport.kernel_dimension => Physics.SMComputableSupport.kernel_dimension,
  GUT.SMComputableSupport.kernel_dimension_int => Physics.SMComputableSupport.kernel_dimension_int,
  GUT.SMComputableSupport.local_allowed_iff => Physics.SMComputableSupport.local_allowed_iff,
  GUT.SMComputableSupport.model => Physics.SMComputableSupport.model,
  GUT.SMComputableSupport.nonnegative => Physics.SMComputableSupport.nonnegative,
  GUT.SMComputableSupport.presents => Physics.SMComputableSupport.presents,
  GUT.SMComputableSupport.rank_formula => Physics.SMComputableSupport.rank_formula
]

assert_compatible GUT.SMComputableQLSupport.Conditions => Physics.SMComputableQLSupport.Conditions
assert_compatible GUT.SMComputableQLSupport.EntryAllowed => Physics.SMComputableQLSupport.EntryAllowed
assert_compatible GUT.SMComputableQLSupport.Input => Physics.SMComputableQLSupport.Input
assert_compatible GUT.SMComputableQLSupport.allowed_iff => Physics.SMComputableQLSupport.allowed_iff
assert_compatible GUT.SMComputableQLSupport.entry_allowed_iff => Physics.SMComputableQLSupport.entry_allowed_iff
assert_compatible GUT.SMComputableQLSupport.forbidden_iff => Physics.SMComputableQLSupport.forbidden_iff
assert_compatible GUT.SMComputableQLSupport.original_allowed_iff => Physics.SMComputableQLSupport.original_allowed_iff
assert_compatible GUT.SMComputableQLSupport.original_forbidden_iff => Physics.SMComputableQLSupport.original_forbidden_iff
assert_compatible GUT.SMComputableQLSupport.satisfies_iff => Physics.SMComputableQLSupport.satisfies_iff
assert_compatible GUT.SMComputableQLSupport.test => Physics.SMComputableQLSupport.test
assert_compatible GUT.SMComputableQLSupport.test.eq_1 => Physics.SMComputableQLSupport.test.eq_1
assert_compatible GUT.SMComputableQLSupport.test_allowed_iff => Physics.SMComputableQLSupport.test_allowed_iff
assert_compatible GUT.SMComputableSupport.compactBorel => Physics.SMComputableSupport.compactBorel
assert_compatible GUT.SMComputableSupport.compactMeasurable => Physics.SMComputableSupport.compactMeasurable
assert_compatible GUT.SMComputableSupport.kernel_dimension => Physics.SMComputableSupport.kernel_dimension
assert_compatible GUT.SMComputableSupport.kernel_dimension_int => Physics.SMComputableSupport.kernel_dimension_int
assert_compatible GUT.SMComputableSupport.local_allowed_iff => Physics.SMComputableSupport.local_allowed_iff
assert_compatible GUT.SMComputableSupport.model => Physics.SMComputableSupport.model
assert_compatible GUT.SMComputableSupport.nonnegative => Physics.SMComputableSupport.nonnegative
assert_compatible GUT.SMComputableSupport.presents => Physics.SMComputableSupport.presents
assert_compatible GUT.SMComputableSupport.rank_formula => Physics.SMComputableSupport.rank_formula
