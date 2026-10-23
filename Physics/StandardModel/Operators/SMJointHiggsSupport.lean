import Physics.StandardModel.Operators.Support.Joint.SMJointHiggsSupport
import Physics.StandardModel.Operators.SMJointContentSupport
import Physics.StandardModel.Operators.SMLowerHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointHiggsSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointHiggsSupport.HiggsSupport => Physics.SMJointHiggsSupport.HiggsSupport,
  GUT.SMJointHiggsSupport.compactLocalEquiv => Physics.SMJointHiggsSupport.compactLocalEquiv,
  GUT.SMJointHiggsSupport.local_iff => Physics.SMJointHiggsSupport.local_iff,
  GUT.SMJointHiggsSupport.original_ql_forbidden_iff => Physics.SMJointHiggsSupport.original_ql_forbidden_iff,
  GUT.SMJointHiggsSupport.original_ql_iff => Physics.SMJointHiggsSupport.original_ql_iff,
  GUT.SMJointHiggsSupport.restrictCoefficient => Physics.SMJointHiggsSupport.restrictCoefficient,
  GUT.SMJointHiggsSupport.restricted_allowed => Physics.SMJointHiggsSupport.restricted_allowed
]

assert_compatible GUT.SMJointHiggsSupport.HiggsSupport => Physics.SMJointHiggsSupport.HiggsSupport
assert_compatible GUT.SMJointHiggsSupport.compactLocalEquiv => Physics.SMJointHiggsSupport.compactLocalEquiv
assert_compatible GUT.SMJointHiggsSupport.local_iff => Physics.SMJointHiggsSupport.local_iff
assert_compatible GUT.SMJointHiggsSupport.original_ql_forbidden_iff => Physics.SMJointHiggsSupport.original_ql_forbidden_iff
assert_compatible GUT.SMJointHiggsSupport.original_ql_iff => Physics.SMJointHiggsSupport.original_ql_iff
assert_compatible GUT.SMJointHiggsSupport.restrictCoefficient => Physics.SMJointHiggsSupport.restrictCoefficient
assert_compatible GUT.SMJointHiggsSupport.restricted_allowed => Physics.SMJointHiggsSupport.restricted_allowed
