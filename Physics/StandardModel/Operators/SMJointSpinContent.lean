import Physics.StandardModel.Operators.Support.Joint.SMJointSpinContent
import Physics.StandardModel.Operators.SMJointWeakContent
import Physics.StandardModel.Operators.SMCompactSpinBound
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointSpinContent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointSpinContent.ColorHyper => Physics.SMJointSpinContent.ColorHyper,
  GUT.SMJointSpinContent.JointMultiplicity => Physics.SMJointSpinContent.JointMultiplicity,
  GUT.SMJointSpinContent.LeftMultiplicity => Physics.SMJointSpinContent.LeftMultiplicity,
  GUT.SMJointSpinContent.LeftRemaining => Physics.SMJointSpinContent.LeftRemaining,
  GUT.SMJointSpinContent.jointMultiplicity => Physics.SMJointSpinContent.jointMultiplicity,
  GUT.SMJointSpinContent.joint_continuous => Physics.SMJointSpinContent.joint_continuous,
  GUT.SMJointSpinContent.leftBorel => Physics.SMJointSpinContent.leftBorel,
  GUT.SMJointSpinContent.leftDecomposition => Physics.SMJointSpinContent.leftDecomposition,
  GUT.SMJointSpinContent.leftMeasurable => Physics.SMJointSpinContent.leftMeasurable,
  GUT.SMJointSpinContent.leftMultiplicity => Physics.SMJointSpinContent.leftMultiplicity,
  GUT.SMJointSpinContent.leftReorder => Physics.SMJointSpinContent.leftReorder,
  GUT.SMJointSpinContent.leftSource => Physics.SMJointSpinContent.leftSource,
  GUT.SMJointSpinContent.left_bounded => Physics.SMJointSpinContent.left_bounded,
  GUT.SMJointSpinContent.left_continuous => Physics.SMJointSpinContent.left_continuous,
  GUT.SMJointSpinContent.left_inverse_continuous => Physics.SMJointSpinContent.left_inverse_continuous,
  GUT.SMJointSpinContent.left_multiplicity_continuous => Physics.SMJointSpinContent.left_multiplicity_continuous,
  GUT.SMJointSpinContent.remainingBorel => Physics.SMJointSpinContent.remainingBorel,
  GUT.SMJointSpinContent.remainingMeasurable => Physics.SMJointSpinContent.remainingMeasurable,
  GUT.SMJointSpinContent.remainingTorus => Physics.SMJointSpinContent.remainingTorus,
  GUT.SMJointSpinContent.rightDecomposition => Physics.SMJointSpinContent.rightDecomposition,
  GUT.SMJointSpinContent.rightReorder => Physics.SMJointSpinContent.rightReorder,
  GUT.SMJointSpinContent.rightSource => Physics.SMJointSpinContent.rightSource,
  GUT.SMJointSpinContent.rightTorus => Physics.SMJointSpinContent.rightTorus,
  GUT.SMJointSpinContent.right_bounded => Physics.SMJointSpinContent.right_bounded,
  GUT.SMJointSpinContent.right_bounded_in_left => Physics.SMJointSpinContent.right_bounded_in_left,
  GUT.SMJointSpinContent.right_continuous => Physics.SMJointSpinContent.right_continuous,
  GUT.SMJointSpinContent.weak_multiplicity_bounded => Physics.SMJointSpinContent.weak_multiplicity_bounded
]

assert_compatible GUT.SMJointSpinContent.ColorHyper => Physics.SMJointSpinContent.ColorHyper
assert_compatible GUT.SMJointSpinContent.JointMultiplicity => Physics.SMJointSpinContent.JointMultiplicity
assert_compatible GUT.SMJointSpinContent.LeftMultiplicity => Physics.SMJointSpinContent.LeftMultiplicity
assert_compatible GUT.SMJointSpinContent.LeftRemaining => Physics.SMJointSpinContent.LeftRemaining
assert_compatible GUT.SMJointSpinContent.jointMultiplicity => Physics.SMJointSpinContent.jointMultiplicity
assert_compatible GUT.SMJointSpinContent.joint_continuous => Physics.SMJointSpinContent.joint_continuous
assert_compatible GUT.SMJointSpinContent.leftBorel => Physics.SMJointSpinContent.leftBorel
assert_compatible GUT.SMJointSpinContent.leftDecomposition => Physics.SMJointSpinContent.leftDecomposition
assert_compatible GUT.SMJointSpinContent.leftMeasurable => Physics.SMJointSpinContent.leftMeasurable
assert_compatible GUT.SMJointSpinContent.leftMultiplicity => Physics.SMJointSpinContent.leftMultiplicity
assert_compatible GUT.SMJointSpinContent.leftReorder => Physics.SMJointSpinContent.leftReorder
assert_compatible GUT.SMJointSpinContent.leftSource => Physics.SMJointSpinContent.leftSource
assert_compatible GUT.SMJointSpinContent.left_bounded => Physics.SMJointSpinContent.left_bounded
assert_compatible GUT.SMJointSpinContent.left_continuous => Physics.SMJointSpinContent.left_continuous
assert_compatible GUT.SMJointSpinContent.left_inverse_continuous => Physics.SMJointSpinContent.left_inverse_continuous
assert_compatible GUT.SMJointSpinContent.left_multiplicity_continuous => Physics.SMJointSpinContent.left_multiplicity_continuous
assert_compatible GUT.SMJointSpinContent.remainingBorel => Physics.SMJointSpinContent.remainingBorel
assert_compatible GUT.SMJointSpinContent.remainingMeasurable => Physics.SMJointSpinContent.remainingMeasurable
assert_compatible GUT.SMJointSpinContent.remainingTorus => Physics.SMJointSpinContent.remainingTorus
assert_compatible GUT.SMJointSpinContent.rightDecomposition => Physics.SMJointSpinContent.rightDecomposition
assert_compatible GUT.SMJointSpinContent.rightReorder => Physics.SMJointSpinContent.rightReorder
assert_compatible GUT.SMJointSpinContent.rightSource => Physics.SMJointSpinContent.rightSource
assert_compatible GUT.SMJointSpinContent.rightTorus => Physics.SMJointSpinContent.rightTorus
assert_compatible GUT.SMJointSpinContent.right_bounded => Physics.SMJointSpinContent.right_bounded
assert_compatible GUT.SMJointSpinContent.right_bounded_in_left => Physics.SMJointSpinContent.right_bounded_in_left
assert_compatible GUT.SMJointSpinContent.right_continuous => Physics.SMJointSpinContent.right_continuous
assert_compatible GUT.SMJointSpinContent.weak_multiplicity_bounded => Physics.SMJointSpinContent.weak_multiplicity_bounded
