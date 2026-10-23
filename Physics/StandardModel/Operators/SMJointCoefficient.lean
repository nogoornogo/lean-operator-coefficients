import Physics.StandardModel.Operators.Support.Joint.SMJointCoefficient
import Physics.StandardModel.Operators.SMJointOccurrence
import Math.RepresentationTheory.SU2FiniteCoupling
import Math.RepresentationTheory.CharacterTwistTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointCoefficient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointCoefficient.character => Physics.SMJointCoefficient.character,
  GUT.SMJointCoefficient.character_eq => Physics.SMJointCoefficient.character_eq,
  GUT.SMJointCoefficient.collapsedSpin => Physics.SMJointCoefficient.collapsedSpin,
  GUT.SMJointCoefficient.collapsedTarget => Physics.SMJointCoefficient.collapsedTarget,
  GUT.SMJointCoefficient.colorHyperProjection => Physics.SMJointCoefficient.colorHyperProjection,
  GUT.SMJointCoefficient.inverseBoson => Physics.SMJointCoefficient.inverseBoson,
  GUT.SMJointCoefficient.line => Physics.SMJointCoefficient.line,
  GUT.SMJointCoefficient.local_allowed_iff => Physics.SMJointCoefficient.local_allowed_iff,
  GUT.SMJointCoefficient.phase => Physics.SMJointCoefficient.phase,
  GUT.SMJointCoefficient.targetEquiv => Physics.SMJointCoefficient.targetEquiv,
  GUT.SMJointCoefficient.weakModel => Physics.SMJointCoefficient.weakModel,
  GUT.SMJointCoefficient.weakSelfDual => Physics.SMJointCoefficient.weakSelfDual
]

assert_compatible GUT.SMJointCoefficient.character => Physics.SMJointCoefficient.character
assert_compatible GUT.SMJointCoefficient.character_eq => Physics.SMJointCoefficient.character_eq
assert_compatible GUT.SMJointCoefficient.collapsedSpin => Physics.SMJointCoefficient.collapsedSpin
assert_compatible GUT.SMJointCoefficient.collapsedTarget => Physics.SMJointCoefficient.collapsedTarget
assert_compatible GUT.SMJointCoefficient.colorHyperProjection => Physics.SMJointCoefficient.colorHyperProjection
assert_compatible GUT.SMJointCoefficient.inverseBoson => Physics.SMJointCoefficient.inverseBoson
assert_compatible GUT.SMJointCoefficient.line => Physics.SMJointCoefficient.line
assert_compatible GUT.SMJointCoefficient.local_allowed_iff => Physics.SMJointCoefficient.local_allowed_iff
assert_compatible GUT.SMJointCoefficient.phase => Physics.SMJointCoefficient.phase
assert_compatible GUT.SMJointCoefficient.targetEquiv => Physics.SMJointCoefficient.targetEquiv
assert_compatible GUT.SMJointCoefficient.weakModel => Physics.SMJointCoefficient.weakModel
assert_compatible GUT.SMJointCoefficient.weakSelfDual => Physics.SMJointCoefficient.weakSelfDual
