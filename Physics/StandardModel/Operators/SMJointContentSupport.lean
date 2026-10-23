import Physics.StandardModel.Operators.Support.Joint.SMJointContentSupport
import Math.RepresentationTheory.JointContentPresentation
import Physics.StandardModel.Operators.SMSignedCoreJointPresentation
import Physics.StandardModel.Operators.SMIteratedContent
import Physics.StandardModel.Operators.SMGenerationCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointContentSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointContentSupport.Supports => Physics.SMJointContentSupport.Supports,
  GUT.SMJointContentSupport.actionEquiv => Physics.SMJointContentSupport.actionEquiv,
  GUT.SMJointContentSupport.cores => Physics.SMJointContentSupport.cores,
  GUT.SMJointContentSupport.expression => Physics.SMJointContentSupport.expression,
  GUT.SMJointContentSupport.field_restrict => Physics.SMJointContentSupport.field_restrict,
  GUT.SMJointContentSupport.leaves => Physics.SMJointContentSupport.leaves,
  GUT.SMJointContentSupport.restricted_iff => Physics.SMJointContentSupport.restricted_iff,
  GUT.SMJointContentSupport.sourceEquiv => Physics.SMJointContentSupport.sourceEquiv,
  GUT.SMJointContentSupport.source_restrict => Physics.SMJointContentSupport.source_restrict,
  GUT.SMJointContentSupport.supports_iff_choices => Physics.SMJointContentSupport.supports_iff_choices,
  GUT.SMJointContentSupport.tree => Physics.SMJointContentSupport.tree
]

assert_compatible GUT.SMJointContentSupport.Supports => Physics.SMJointContentSupport.Supports
assert_compatible GUT.SMJointContentSupport.actionEquiv => Physics.SMJointContentSupport.actionEquiv
assert_compatible GUT.SMJointContentSupport.cores => Physics.SMJointContentSupport.cores
assert_compatible GUT.SMJointContentSupport.expression => Physics.SMJointContentSupport.expression
assert_compatible GUT.SMJointContentSupport.field_restrict => Physics.SMJointContentSupport.field_restrict
assert_compatible GUT.SMJointContentSupport.leaves => Physics.SMJointContentSupport.leaves
assert_compatible GUT.SMJointContentSupport.restricted_iff => Physics.SMJointContentSupport.restricted_iff
assert_compatible GUT.SMJointContentSupport.sourceEquiv => Physics.SMJointContentSupport.sourceEquiv
assert_compatible GUT.SMJointContentSupport.source_restrict => Physics.SMJointContentSupport.source_restrict
assert_compatible GUT.SMJointContentSupport.supports_iff_choices => Physics.SMJointContentSupport.supports_iff_choices
assert_compatible GUT.SMJointContentSupport.tree => Physics.SMJointContentSupport.tree
