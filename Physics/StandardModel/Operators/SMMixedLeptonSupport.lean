import Physics.StandardModel.Operators.Support.Joint.SMMixedLeptonSupport
import Physics.StandardModel.Operators.SMMixedLeptonDictionary
import Physics.StandardModel.Operators.SMLeptonMaximalLocal
import Physics.StandardModel.Operators.SMLocalCoefficientGluing
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMMixedLeptonSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMMixedLeptonSupport.distance => Physics.SMMixedLeptonSupport.distance,
  GUT.SMMixedLeptonSupport.local_iff => Physics.SMMixedLeptonSupport.local_iff,
  GUT.SMMixedLeptonSupport.maximal_triangle => Physics.SMMixedLeptonSupport.maximal_triangle,
  GUT.SMMixedLeptonSupport.original_ql_iff => Physics.SMMixedLeptonSupport.original_ql_iff
]

assert_compatible GUT.SMMixedLeptonSupport.distance => Physics.SMMixedLeptonSupport.distance
assert_compatible GUT.SMMixedLeptonSupport.local_iff => Physics.SMMixedLeptonSupport.local_iff
assert_compatible GUT.SMMixedLeptonSupport.maximal_triangle => Physics.SMMixedLeptonSupport.maximal_triangle
assert_compatible GUT.SMMixedLeptonSupport.original_ql_iff => Physics.SMMixedLeptonSupport.original_ql_iff
