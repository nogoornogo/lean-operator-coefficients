import Physics.StandardModel.Operators.Support.Quark.SMQLPartialKernel
import Physics.StandardModel.Operators.SMWeylFiniteKernel
import Math.RepresentationTheory.PartialInvariantKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQLPartialKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQLPartialKernel.Space => Physics.SMQLPartialKernel.Space,
  GUT.SMQLPartialKernel.coefficientEquiv => Physics.SMQLPartialKernel.coefficientEquiv,
  GUT.SMQLPartialKernel.localAction => Physics.SMQLPartialKernel.localAction,
  GUT.SMQLPartialKernel.local_allowed_iff => Physics.SMQLPartialKernel.local_allowed_iff,
  GUT.SMQLPartialKernel.original_allowed_iff => Physics.SMQLPartialKernel.original_allowed_iff
]

assert_compatible GUT.SMQLPartialKernel.Space => Physics.SMQLPartialKernel.Space
assert_compatible GUT.SMQLPartialKernel.coefficientEquiv => Physics.SMQLPartialKernel.coefficientEquiv
assert_compatible GUT.SMQLPartialKernel.localAction => Physics.SMQLPartialKernel.localAction
assert_compatible GUT.SMQLPartialKernel.local_allowed_iff => Physics.SMQLPartialKernel.local_allowed_iff
assert_compatible GUT.SMQLPartialKernel.original_allowed_iff => Physics.SMQLPartialKernel.original_allowed_iff
