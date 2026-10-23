import Physics.StandardModel.Operators.Support.Joint.SMMixedFamilySupport
import Physics.StandardModel.Operators.FourFamilyHiggsContent
import Physics.StandardModel.Operators.SMLowerHiggsSupport
import Physics.StandardModel.Operators.SMMixedConjugation
import Math.RepresentationTheory.MixedSupportSeparation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedFamilySupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMMixedFamilySupport.conjugate_original_ql_forbidden => Physics.SMMixedFamilySupport.conjugate_original_ql_forbidden,
  GUT.SMMixedFamilySupport.conjugate_original_ql_iff => Physics.SMMixedFamilySupport.conjugate_original_ql_iff,
  GUT.SMMixedFamilySupport.counts_iff => Physics.SMMixedFamilySupport.counts_iff,
  GUT.SMMixedFamilySupport.equiv => Physics.SMMixedFamilySupport.equiv,
  GUT.SMMixedFamilySupport.factorwise_counterexample => Physics.SMMixedFamilySupport.factorwise_counterexample,
  GUT.SMMixedFamilySupport.membership => Physics.SMMixedFamilySupport.membership,
  GUT.SMMixedFamilySupport.oldSpace => Physics.SMMixedFamilySupport.oldSpace,
  GUT.SMMixedFamilySupport.originalSpace => Physics.SMMixedFamilySupport.originalSpace,
  GUT.SMMixedFamilySupport.original_ql_forbidden => Physics.SMMixedFamilySupport.original_ql_forbidden,
  GUT.SMMixedFamilySupport.original_ql_iff => Physics.SMMixedFamilySupport.original_ql_iff,
  GUT.SMMixedFamilySupport.pattern => Physics.SMMixedFamilySupport.pattern
]

assert_compatible GUT.SMMixedFamilySupport.conjugate_original_ql_forbidden => Physics.SMMixedFamilySupport.conjugate_original_ql_forbidden
assert_compatible GUT.SMMixedFamilySupport.conjugate_original_ql_iff => Physics.SMMixedFamilySupport.conjugate_original_ql_iff
assert_compatible GUT.SMMixedFamilySupport.counts_iff => Physics.SMMixedFamilySupport.counts_iff
assert_compatible GUT.SMMixedFamilySupport.equiv => Physics.SMMixedFamilySupport.equiv
assert_compatible GUT.SMMixedFamilySupport.factorwise_counterexample => Physics.SMMixedFamilySupport.factorwise_counterexample
assert_compatible GUT.SMMixedFamilySupport.membership => Physics.SMMixedFamilySupport.membership
assert_compatible GUT.SMMixedFamilySupport.oldSpace => Physics.SMMixedFamilySupport.oldSpace
assert_compatible GUT.SMMixedFamilySupport.originalSpace => Physics.SMMixedFamilySupport.originalSpace
assert_compatible GUT.SMMixedFamilySupport.original_ql_forbidden => Physics.SMMixedFamilySupport.original_ql_forbidden
assert_compatible GUT.SMMixedFamilySupport.original_ql_iff => Physics.SMMixedFamilySupport.original_ql_iff
assert_compatible GUT.SMMixedFamilySupport.pattern => Physics.SMMixedFamilySupport.pattern
