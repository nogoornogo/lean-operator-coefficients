import Physics.StandardModel.Operators.Support.Joint.SMJointColoredSupport
import Physics.StandardModel.Operators.SMJointAlgebraicSupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointColoredSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointColoredSupport.Input => Physics.SMJointColoredSupport.Input,
  GUT.SMJointColoredSupport.axisTerms => Physics.SMJointColoredSupport.axisTerms,
  GUT.SMJointColoredSupport.axisTerms.eq_1 => Physics.SMJointColoredSupport.axisTerms.eq_1,
  GUT.SMJointColoredSupport.axisWeight => Physics.SMJointColoredSupport.axisWeight,
  GUT.SMJointColoredSupport.axisWeight.eq_1 => Physics.SMJointColoredSupport.axisWeight.eq_1,
  GUT.SMJointColoredSupport.axis_evaluation => Physics.SMJointColoredSupport.axis_evaluation,
  GUT.SMJointColoredSupport.compactBorel => Physics.SMJointColoredSupport.compactBorel,
  GUT.SMJointColoredSupport.compactMeasurable => Physics.SMJointColoredSupport.compactMeasurable,
  GUT.SMJointColoredSupport.homModel => Physics.SMJointColoredSupport.homModel,
  GUT.SMJointColoredSupport.homTerms => Physics.SMJointColoredSupport.homTerms,
  GUT.SMJointColoredSupport.joint_allowed_iff => Physics.SMJointColoredSupport.joint_allowed_iff,
  GUT.SMJointColoredSupport.leftInner => Physics.SMJointColoredSupport.leftInner,
  GUT.SMJointColoredSupport.leftNorm => Physics.SMJointColoredSupport.leftNorm,
  GUT.SMJointColoredSupport.monomial_axis => Physics.SMJointColoredSupport.monomial_axis,
  GUT.SMJointColoredSupport.presents => Physics.SMJointColoredSupport.presents,
  GUT.SMJointColoredSupport.reverseTerms => Physics.SMJointColoredSupport.reverseTerms,
  GUT.SMJointColoredSupport.reverseTerms.eq_1 => Physics.SMJointColoredSupport.reverseTerms.eq_1,
  GUT.SMJointColoredSupport.reverse_evaluation => Physics.SMJointColoredSupport.reverse_evaluation,
  GUT.SMJointColoredSupport.rightInner => Physics.SMJointColoredSupport.rightInner,
  GUT.SMJointColoredSupport.rightNorm => Physics.SMJointColoredSupport.rightNorm,
  GUT.SMJointColoredSupport.targetTerms => Physics.SMJointColoredSupport.targetTerms,
  GUT.SMJointColoredSupport.targetTerms.eq_1 => Physics.SMJointColoredSupport.targetTerms.eq_1,
  GUT.SMJointColoredSupport.target_character => Physics.SMJointColoredSupport.target_character,
  GUT.SMJointColoredSupport.target_continuous => Physics.SMJointColoredSupport.target_continuous,
  GUT.SMJointColoredSupport.target_evaluation => Physics.SMJointColoredSupport.target_evaluation
]

assert_compatible GUT.SMJointColoredSupport.Input => Physics.SMJointColoredSupport.Input
assert_compatible GUT.SMJointColoredSupport.axisTerms => Physics.SMJointColoredSupport.axisTerms
assert_compatible GUT.SMJointColoredSupport.axisTerms.eq_1 => Physics.SMJointColoredSupport.axisTerms.eq_1
assert_compatible GUT.SMJointColoredSupport.axisWeight => Physics.SMJointColoredSupport.axisWeight
assert_compatible GUT.SMJointColoredSupport.axisWeight.eq_1 => Physics.SMJointColoredSupport.axisWeight.eq_1
assert_compatible GUT.SMJointColoredSupport.axis_evaluation => Physics.SMJointColoredSupport.axis_evaluation
assert_compatible GUT.SMJointColoredSupport.compactBorel => Physics.SMJointColoredSupport.compactBorel
assert_compatible GUT.SMJointColoredSupport.compactMeasurable => Physics.SMJointColoredSupport.compactMeasurable
assert_compatible GUT.SMJointColoredSupport.homModel => Physics.SMJointColoredSupport.homModel
assert_compatible GUT.SMJointColoredSupport.homTerms => Physics.SMJointColoredSupport.homTerms
assert_compatible GUT.SMJointColoredSupport.joint_allowed_iff => Physics.SMJointColoredSupport.joint_allowed_iff
assert_compatible GUT.SMJointColoredSupport.leftInner => Physics.SMJointColoredSupport.leftInner
assert_compatible GUT.SMJointColoredSupport.leftNorm => Physics.SMJointColoredSupport.leftNorm
assert_compatible GUT.SMJointColoredSupport.monomial_axis => Physics.SMJointColoredSupport.monomial_axis
assert_compatible GUT.SMJointColoredSupport.presents => Physics.SMJointColoredSupport.presents
assert_compatible GUT.SMJointColoredSupport.reverseTerms => Physics.SMJointColoredSupport.reverseTerms
assert_compatible GUT.SMJointColoredSupport.reverseTerms.eq_1 => Physics.SMJointColoredSupport.reverseTerms.eq_1
assert_compatible GUT.SMJointColoredSupport.reverse_evaluation => Physics.SMJointColoredSupport.reverse_evaluation
assert_compatible GUT.SMJointColoredSupport.rightInner => Physics.SMJointColoredSupport.rightInner
assert_compatible GUT.SMJointColoredSupport.rightNorm => Physics.SMJointColoredSupport.rightNorm
assert_compatible GUT.SMJointColoredSupport.targetTerms => Physics.SMJointColoredSupport.targetTerms
assert_compatible GUT.SMJointColoredSupport.targetTerms.eq_1 => Physics.SMJointColoredSupport.targetTerms.eq_1
assert_compatible GUT.SMJointColoredSupport.target_character => Physics.SMJointColoredSupport.target_character
assert_compatible GUT.SMJointColoredSupport.target_continuous => Physics.SMJointColoredSupport.target_continuous
assert_compatible GUT.SMJointColoredSupport.target_evaluation => Physics.SMJointColoredSupport.target_evaluation
