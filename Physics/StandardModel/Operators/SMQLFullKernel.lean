import Physics.StandardModel.Operators.Support.Quark.SMQLFullKernel
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMQLFullKernel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMQLFullKernel.Kernel => Physics.SMQLFullKernel.Kernel,
  GUT.SMQLFullKernel.RankAllowed => Physics.SMQLFullKernel.RankAllowed,
  GUT.SMQLFullKernel.coefficientEquiv => Physics.SMQLFullKernel.coefficientEquiv,
  GUT.SMQLFullKernel.local_allowed_iff => Physics.SMQLFullKernel.local_allowed_iff,
  GUT.SMQLFullKernel.original_allowed_iff => Physics.SMQLFullKernel.original_allowed_iff,
  GUT.SMQLFullKernel.test_allowed_iff => Physics.SMQLFullKernel.test_allowed_iff
]

assert_compatible GUT.SMQLFullKernel.Kernel => Physics.SMQLFullKernel.Kernel
assert_compatible GUT.SMQLFullKernel.RankAllowed => Physics.SMQLFullKernel.RankAllowed
assert_compatible GUT.SMQLFullKernel.coefficientEquiv => Physics.SMQLFullKernel.coefficientEquiv
assert_compatible GUT.SMQLFullKernel.local_allowed_iff => Physics.SMQLFullKernel.local_allowed_iff
assert_compatible GUT.SMQLFullKernel.original_allowed_iff => Physics.SMQLFullKernel.original_allowed_iff
assert_compatible GUT.SMQLFullKernel.test_allowed_iff => Physics.SMQLFullKernel.test_allowed_iff
