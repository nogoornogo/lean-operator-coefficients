import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteConstituentSupport
import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Physics.StandardModel.Operators.QLFiniteSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMFiniteConstituentSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCombinedCompactContinuity.bosonModel.eq_1 => Physics.SMCombinedCompactContinuity.bosonModel.eq_1,
  GUT.SMFiniteConstituentSupport.Matches => Physics.SMFiniteConstituentSupport.Matches,
  GUT.SMFiniteConstituentSupport.blocks_bounded => Physics.SMFiniteConstituentSupport.blocks_bounded,
  GUT.SMFiniteConstituentSupport.boson_irreducible => Physics.SMFiniteConstituentSupport.boson_irreducible,
  GUT.SMFiniteConstituentSupport.boson_restrict => Physics.SMFiniteConstituentSupport.boson_restrict,
  GUT.SMFiniteConstituentSupport.compactBorel => Physics.SMFiniteConstituentSupport.compactBorel,
  GUT.SMFiniteConstituentSupport.compactMeasurable => Physics.SMFiniteConstituentSupport.compactMeasurable,
  GUT.SMFiniteConstituentSupport.decomposition => Physics.SMFiniteConstituentSupport.decomposition,
  GUT.SMFiniteConstituentSupport.kernel_allowed_iff => Physics.SMFiniteConstituentSupport.kernel_allowed_iff,
  GUT.SMFiniteConstituentSupport.local_allowed_iff => Physics.SMFiniteConstituentSupport.local_allowed_iff,
  GUT.SMFiniteConstituentSupport.original_ql_forbidden => Physics.SMFiniteConstituentSupport.original_ql_forbidden,
  GUT.SMFiniteConstituentSupport.original_ql_iff => Physics.SMFiniteConstituentSupport.original_ql_iff,
  GUT.SMFiniteConstituentSupport.ql_test_iff => Physics.SMFiniteConstituentSupport.ql_test_iff,
  GUT.SMFiniteConstituentSupport.source => Physics.SMFiniteConstituentSupport.source,
  GUT.SMFiniteConstituentSupport.weakInclusion => Physics.SMFiniteConstituentSupport.weakInclusion,
  GUT.SMFiniteConstituentSupport.weakInclusion.eq_1 => Physics.SMFiniteConstituentSupport.weakInclusion.eq_1
]

assert_compatible GUT.SMCombinedCompactContinuity.bosonModel.eq_1 => Physics.SMCombinedCompactContinuity.bosonModel.eq_1
assert_compatible GUT.SMFiniteConstituentSupport.Matches => Physics.SMFiniteConstituentSupport.Matches
assert_compatible GUT.SMFiniteConstituentSupport.blocks_bounded => Physics.SMFiniteConstituentSupport.blocks_bounded
assert_compatible GUT.SMFiniteConstituentSupport.boson_irreducible => Physics.SMFiniteConstituentSupport.boson_irreducible
assert_compatible GUT.SMFiniteConstituentSupport.boson_restrict => Physics.SMFiniteConstituentSupport.boson_restrict
assert_compatible GUT.SMFiniteConstituentSupport.compactBorel => Physics.SMFiniteConstituentSupport.compactBorel
assert_compatible GUT.SMFiniteConstituentSupport.compactMeasurable => Physics.SMFiniteConstituentSupport.compactMeasurable
assert_compatible GUT.SMFiniteConstituentSupport.decomposition => Physics.SMFiniteConstituentSupport.decomposition
assert_compatible GUT.SMFiniteConstituentSupport.kernel_allowed_iff => Physics.SMFiniteConstituentSupport.kernel_allowed_iff
assert_compatible GUT.SMFiniteConstituentSupport.local_allowed_iff => Physics.SMFiniteConstituentSupport.local_allowed_iff
assert_compatible GUT.SMFiniteConstituentSupport.original_ql_forbidden => Physics.SMFiniteConstituentSupport.original_ql_forbidden
assert_compatible GUT.SMFiniteConstituentSupport.original_ql_iff => Physics.SMFiniteConstituentSupport.original_ql_iff
assert_compatible GUT.SMFiniteConstituentSupport.ql_test_iff => Physics.SMFiniteConstituentSupport.ql_test_iff
assert_compatible GUT.SMFiniteConstituentSupport.source => Physics.SMFiniteConstituentSupport.source
assert_compatible GUT.SMFiniteConstituentSupport.weakInclusion => Physics.SMFiniteConstituentSupport.weakInclusion
assert_compatible GUT.SMFiniteConstituentSupport.weakInclusion.eq_1 => Physics.SMFiniteConstituentSupport.weakInclusion.eq_1
