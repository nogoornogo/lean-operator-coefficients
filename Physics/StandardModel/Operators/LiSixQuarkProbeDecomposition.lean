import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkProbeDecomposition
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkProbeDecomposition instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkExtension.LocalArray => Physics.LiSixQuarkExtension.LocalArray,
  GUT.LiSixQuarkExtension.decomposition_unique => Physics.LiSixQuarkExtension.decomposition_unique,
  GUT.LiSixQuarkExtension.probeDecomposition => Physics.LiSixQuarkExtension.probeDecomposition,
  GUT.LiSixQuarkExtension.probe_kernel_finrank => Physics.LiSixQuarkExtension.probe_kernel_finrank,
  GUT.LiSixQuarkExtension.reconstruct_withoutExtra => Physics.LiSixQuarkExtension.reconstruct_withoutExtra,
  GUT.LiSixQuarkExtension.withoutExtra => Physics.LiSixQuarkExtension.withoutExtra,
  GUT.LiSixQuarkExtension.withoutExtra_mem_kernel => Physics.LiSixQuarkExtension.withoutExtra_mem_kernel
]

assert_compatible GUT.LiSixQuarkExtension.LocalArray => Physics.LiSixQuarkExtension.LocalArray
assert_compatible GUT.LiSixQuarkExtension.decomposition_unique => Physics.LiSixQuarkExtension.decomposition_unique
assert_compatible GUT.LiSixQuarkExtension.probeDecomposition => Physics.LiSixQuarkExtension.probeDecomposition
assert_compatible GUT.LiSixQuarkExtension.probe_kernel_finrank => Physics.LiSixQuarkExtension.probe_kernel_finrank
assert_compatible GUT.LiSixQuarkExtension.reconstruct_withoutExtra => Physics.LiSixQuarkExtension.reconstruct_withoutExtra
assert_compatible GUT.LiSixQuarkExtension.withoutExtra => Physics.LiSixQuarkExtension.withoutExtra
assert_compatible GUT.LiSixQuarkExtension.withoutExtra_mem_kernel => Physics.LiSixQuarkExtension.withoutExtra_mem_kernel
