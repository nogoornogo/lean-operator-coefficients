import Physics.StandardModel.Operators.Support.Joint.SMSignedBalance
import Math.RepresentationTheory.PatternCountSum
import Physics.StandardModel.Operators.SMSaturatedContentSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMSignedBalance instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMSignedBalance.Balanced => Physics.SMSignedBalance.Balanced,
  GUT.SMSignedBalance.full_balanced => Physics.SMSignedBalance.full_balanced,
  GUT.SMSignedBalance.full_original_ql_iff => Physics.SMSignedBalance.full_original_ql_iff,
  GUT.SMSignedBalance.hypercharge_zero => Physics.SMSignedBalance.hypercharge_zero,
  GUT.SMSignedBalance.ql_charge_zero => Physics.SMSignedBalance.ql_charge_zero,
  GUT.SMSignedBalance.saturated_original_ql_iff => Physics.SMSignedBalance.saturated_original_ql_iff
]

assert_compatible GUT.SMSignedBalance.Balanced => Physics.SMSignedBalance.Balanced
assert_compatible GUT.SMSignedBalance.full_balanced => Physics.SMSignedBalance.full_balanced
assert_compatible GUT.SMSignedBalance.full_original_ql_iff => Physics.SMSignedBalance.full_original_ql_iff
assert_compatible GUT.SMSignedBalance.hypercharge_zero => Physics.SMSignedBalance.hypercharge_zero
assert_compatible GUT.SMSignedBalance.ql_charge_zero => Physics.SMSignedBalance.ql_charge_zero
assert_compatible GUT.SMSignedBalance.saturated_original_ql_iff => Physics.SMSignedBalance.saturated_original_ql_iff
