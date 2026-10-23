import Physics.StandardModel.Operators.Support.Coordinates.SMChargedKernelRank
import Physics.StandardModel.Operators.SMFullLocalKernel
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMChargedKernelRank instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMChargedKernelRank.dimension_zero_above_cutoff => Physics.SMChargedKernelRank.dimension_zero_above_cutoff,
  GUT.SMChargedKernelRank.full_rank => Physics.SMChargedKernelRank.full_rank,
  GUT.SMChargedKernelRank.local_charge => Physics.SMChargedKernelRank.local_charge,
  GUT.SMChargedKernelRank.rank_zero_above_cutoff => Physics.SMChargedKernelRank.rank_zero_above_cutoff
]

assert_compatible GUT.SMChargedKernelRank.dimension_zero_above_cutoff => Physics.SMChargedKernelRank.dimension_zero_above_cutoff
assert_compatible GUT.SMChargedKernelRank.full_rank => Physics.SMChargedKernelRank.full_rank
assert_compatible GUT.SMChargedKernelRank.local_charge => Physics.SMChargedKernelRank.local_charge
assert_compatible GUT.SMChargedKernelRank.rank_zero_above_cutoff => Physics.SMChargedKernelRank.rank_zero_above_cutoff
