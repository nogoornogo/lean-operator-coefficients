import Physics.StandardModel.Operators.Support.Decomposition.SMCompactSupportDecision
import Math.RepresentationTheory.CompactGenerationOccupations
import Physics.StandardModel.Operators.SMJointHiggsSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMCompactSupportDecision instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCompactSupportDecision.colorDecision => Physics.SMCompactSupportDecision.colorDecision,
  GUT.SMCompactSupportDecision.contentDecision => Physics.SMCompactSupportDecision.contentDecision,
  GUT.SMCompactSupportDecision.diagramDecision => Physics.SMCompactSupportDecision.diagramDecision,
  GUT.SMCompactSupportDecision.expressionDecision => Physics.SMCompactSupportDecision.expressionDecision,
  GUT.SMCompactSupportDecision.higgsDecision => Physics.SMCompactSupportDecision.higgsDecision,
  GUT.SMCompactSupportDecision.jointDecision => Physics.SMCompactSupportDecision.jointDecision,
  GUT.SMCompactSupportDecision.negativeDecision => Physics.SMCompactSupportDecision.negativeDecision,
  GUT.SMCompactSupportDecision.ownerEq => Physics.SMCompactSupportDecision.ownerEq,
  GUT.SMCompactSupportDecision.positiveDecision => Physics.SMCompactSupportDecision.positiveDecision,
  GUT.SMCompactSupportDecision.su2Decision => Physics.SMCompactSupportDecision.su2Decision
]

assert_compatible GUT.SMCompactSupportDecision.colorDecision => Physics.SMCompactSupportDecision.colorDecision
assert_compatible GUT.SMCompactSupportDecision.contentDecision => Physics.SMCompactSupportDecision.contentDecision
assert_compatible GUT.SMCompactSupportDecision.diagramDecision => Physics.SMCompactSupportDecision.diagramDecision
assert_compatible GUT.SMCompactSupportDecision.expressionDecision => Physics.SMCompactSupportDecision.expressionDecision
assert_compatible GUT.SMCompactSupportDecision.higgsDecision => Physics.SMCompactSupportDecision.higgsDecision
assert_compatible GUT.SMCompactSupportDecision.jointDecision => Physics.SMCompactSupportDecision.jointDecision
assert_compatible GUT.SMCompactSupportDecision.negativeDecision => Physics.SMCompactSupportDecision.negativeDecision
assert_compatible GUT.SMCompactSupportDecision.ownerEq => Physics.SMCompactSupportDecision.ownerEq
assert_compatible GUT.SMCompactSupportDecision.positiveDecision => Physics.SMCompactSupportDecision.positiveDecision
assert_compatible GUT.SMCompactSupportDecision.su2Decision => Physics.SMCompactSupportDecision.su2Decision
