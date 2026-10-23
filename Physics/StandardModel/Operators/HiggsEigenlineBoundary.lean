import Physics.StandardModel.Operators.Higgs.HiggsEigenlineBoundary
import Physics.StandardModel.Operators.WeinbergFullSeed
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Higgs.HiggsEigenlineBoundary instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsEigenlineBoundary.no_zero_degree_iff => Physics.HiggsEigenlineBoundary.no_zero_degree_iff,
  GUT.HiggsEigenlineBoundary.two_higgs_allowed => Physics.HiggsEigenlineBoundary.two_higgs_allowed,
  GUT.HiggsEigenlineBoundary.zero_higgs_forbidden => Physics.HiggsEigenlineBoundary.zero_higgs_forbidden
]

assert_compatible GUT.HiggsEigenlineBoundary.no_zero_degree_iff => Physics.HiggsEigenlineBoundary.no_zero_degree_iff
assert_compatible GUT.HiggsEigenlineBoundary.two_higgs_allowed => Physics.HiggsEigenlineBoundary.two_higgs_allowed
assert_compatible GUT.HiggsEigenlineBoundary.zero_higgs_forbidden => Physics.HiggsEigenlineBoundary.zero_higgs_forbidden
