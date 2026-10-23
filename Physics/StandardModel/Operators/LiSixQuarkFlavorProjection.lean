import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFlavorProjection
import Physics.StandardModel.Operators.LiSixQuarkPrintedSpan
import Physics.StandardModel.Operators.SixQuarkTypedFlavor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkFlavorProjection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkFlavorProjection.missing => Physics.LiSixQuarkFlavorProjection.missing,
  GUT.LiSixQuarkFlavorProjection.missing_exchange => Physics.LiSixQuarkFlavorProjection.missing_exchange,
  GUT.LiSixQuarkFlavorProjection.missing_zero_iff_printed => Physics.LiSixQuarkFlavorProjection.missing_zero_iff_printed
]

assert_compatible GUT.LiSixQuarkFlavorProjection.missing => Physics.LiSixQuarkFlavorProjection.missing
assert_compatible GUT.LiSixQuarkFlavorProjection.missing_exchange => Physics.LiSixQuarkFlavorProjection.missing_exchange
assert_compatible GUT.LiSixQuarkFlavorProjection.missing_zero_iff_printed => Physics.LiSixQuarkFlavorProjection.missing_zero_iff_printed
