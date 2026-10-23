import Physics.StandardModel.Operators.Support.Coordinates.SMParityKernelRank
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.RepresentationTheory.MixedScalarSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMParityKernelRank instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMParityKernelRank.action_minus => Physics.SMParityKernelRank.action_minus,
  GUT.SMParityKernelRank.forbidden => Physics.SMParityKernelRank.forbidden,
  GUT.SMParityKernelRank.full_rank => Physics.SMParityKernelRank.full_rank,
  GUT.SMParityKernelRank.raw_minus => Physics.SMParityKernelRank.raw_minus,
  GUT.SMParityKernelRank.source_minus => Physics.SMParityKernelRank.source_minus
]

assert_compatible GUT.SMParityKernelRank.action_minus => Physics.SMParityKernelRank.action_minus
assert_compatible GUT.SMParityKernelRank.forbidden => Physics.SMParityKernelRank.forbidden
assert_compatible GUT.SMParityKernelRank.full_rank => Physics.SMParityKernelRank.full_rank
assert_compatible GUT.SMParityKernelRank.raw_minus => Physics.SMParityKernelRank.raw_minus
assert_compatible GUT.SMParityKernelRank.source_minus => Physics.SMParityKernelRank.source_minus
