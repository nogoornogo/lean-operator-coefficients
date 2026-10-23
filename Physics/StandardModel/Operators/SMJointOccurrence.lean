import Physics.StandardModel.Operators.Support.Joint.SMJointOccurrence
import Physics.StandardModel.Operators.SMJointSpinContent
import Math.RepresentationTheory.SU2IsotypicMatching
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointOccurrence instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointOccurrence.hom_allowed_iff => Physics.SMJointOccurrence.hom_allowed_iff,
  GUT.SMJointOccurrence.leftTarget => Physics.SMJointOccurrence.leftTarget,
  GUT.SMJointOccurrence.rightTarget => Physics.SMJointOccurrence.rightTarget,
  GUT.SMJointOccurrence.target => Physics.SMJointOccurrence.target,
  GUT.SMJointOccurrence.weakTarget => Physics.SMJointOccurrence.weakTarget
]

assert_compatible GUT.SMJointOccurrence.hom_allowed_iff => Physics.SMJointOccurrence.hom_allowed_iff
assert_compatible GUT.SMJointOccurrence.leftTarget => Physics.SMJointOccurrence.leftTarget
assert_compatible GUT.SMJointOccurrence.rightTarget => Physics.SMJointOccurrence.rightTarget
assert_compatible GUT.SMJointOccurrence.target => Physics.SMJointOccurrence.target
assert_compatible GUT.SMJointOccurrence.weakTarget => Physics.SMJointOccurrence.weakTarget
