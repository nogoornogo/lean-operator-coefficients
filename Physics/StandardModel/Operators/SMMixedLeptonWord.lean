import Physics.StandardModel.Operators.Support.Joint.SMMixedLeptonWord
import Physics.StandardModel.Operators.SMMixedLeptonSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedLeptonWord instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMMixedLeptonWord.balanced_ql_iff => Physics.SMMixedLeptonWord.balanced_ql_iff,
  GUT.SMMixedLeptonWord.original_eq => Physics.SMMixedLeptonWord.original_eq,
  GUT.SMMixedLeptonWord.original_ql_iff => Physics.SMMixedLeptonWord.original_ql_iff
]

assert_compatible GUT.SMMixedLeptonWord.balanced_ql_iff => Physics.SMMixedLeptonWord.balanced_ql_iff
assert_compatible GUT.SMMixedLeptonWord.original_eq => Physics.SMMixedLeptonWord.original_eq
assert_compatible GUT.SMMixedLeptonWord.original_ql_iff => Physics.SMMixedLeptonWord.original_ql_iff
