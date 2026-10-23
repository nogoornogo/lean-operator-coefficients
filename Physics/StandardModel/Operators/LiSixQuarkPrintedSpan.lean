import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPrintedSpan
import Physics.StandardModel.Operators.LiSixQuarkLocalBasis
import Physics.StandardModel.Operators.LiSixQuarkProbeDecomposition
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPrintedSpan instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkExtension.extraProbeLinear.eq_1 => Physics.LiSixQuarkExtension.extraProbeLinear.eq_1,
  GUT.LiSixQuarkPrintedSpan.Array => Physics.LiSixQuarkPrintedSpan.Array,
  GUT.LiSixQuarkPrintedSpan.last_orbit => Physics.LiSixQuarkPrintedSpan.last_orbit,
  GUT.LiSixQuarkPrintedSpan.printedSpan => Physics.LiSixQuarkPrintedSpan.printedSpan,
  GUT.LiSixQuarkPrintedSpan.printedSpan_eq_kernel => Physics.LiSixQuarkPrintedSpan.printedSpan_eq_kernel,
  GUT.LiSixQuarkPrintedSpan.printedSpan_le_kernel => Physics.LiSixQuarkPrintedSpan.printedSpan_le_kernel,
  GUT.LiSixQuarkPrintedSpan.printed_finrank => Physics.LiSixQuarkPrintedSpan.printed_finrank,
  GUT.LiSixQuarkPrintedSpan.printed_reconstruction => Physics.LiSixQuarkPrintedSpan.printed_reconstruction,
  GUT.LiSixQuarkPrintedSpan.probe_assembly => Physics.LiSixQuarkPrintedSpan.probe_assembly,
  GUT.LiSixQuarkPrintedSpan.selected_printed => Physics.LiSixQuarkPrintedSpan.selected_printed
]

assert_compatible GUT.LiSixQuarkExtension.extraProbeLinear.eq_1 => Physics.LiSixQuarkExtension.extraProbeLinear.eq_1
assert_compatible GUT.LiSixQuarkPrintedSpan.Array => Physics.LiSixQuarkPrintedSpan.Array
assert_compatible GUT.LiSixQuarkPrintedSpan.last_orbit => Physics.LiSixQuarkPrintedSpan.last_orbit
assert_compatible GUT.LiSixQuarkPrintedSpan.printedSpan => Physics.LiSixQuarkPrintedSpan.printedSpan
assert_compatible GUT.LiSixQuarkPrintedSpan.printedSpan_eq_kernel => Physics.LiSixQuarkPrintedSpan.printedSpan_eq_kernel
assert_compatible GUT.LiSixQuarkPrintedSpan.printedSpan_le_kernel => Physics.LiSixQuarkPrintedSpan.printedSpan_le_kernel
assert_compatible GUT.LiSixQuarkPrintedSpan.printed_finrank => Physics.LiSixQuarkPrintedSpan.printed_finrank
assert_compatible GUT.LiSixQuarkPrintedSpan.printed_reconstruction => Physics.LiSixQuarkPrintedSpan.printed_reconstruction
assert_compatible GUT.LiSixQuarkPrintedSpan.probe_assembly => Physics.LiSixQuarkPrintedSpan.probe_assembly
assert_compatible GUT.LiSixQuarkPrintedSpan.selected_printed => Physics.LiSixQuarkPrintedSpan.selected_printed
