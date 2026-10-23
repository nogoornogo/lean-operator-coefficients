import Physics.StandardModel.Operators.Support.Joint.SMSignedCoreJointPresentation
import Physics.StandardModel.Operators.SMQJointPresentation
import Physics.StandardModel.Operators.SMColoredJointPresentation
import Physics.StandardModel.Operators.SMLeptonJointPresentation
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMSignedCoreJointPresentation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMSignedCoreJointPresentation.allowed_iff => Physics.SMSignedCoreJointPresentation.allowed_iff,
  GUT.SMSignedCoreJointPresentation.forbidden_iff => Physics.SMSignedCoreJointPresentation.forbidden_iff,
  GUT.SMSignedCoreJointPresentation.presentation => Physics.SMSignedCoreJointPresentation.presentation
]

assert_compatible GUT.SMSignedCoreJointPresentation.allowed_iff => Physics.SMSignedCoreJointPresentation.allowed_iff
assert_compatible GUT.SMSignedCoreJointPresentation.forbidden_iff => Physics.SMSignedCoreJointPresentation.forbidden_iff
assert_compatible GUT.SMSignedCoreJointPresentation.presentation => Physics.SMSignedCoreJointPresentation.presentation
