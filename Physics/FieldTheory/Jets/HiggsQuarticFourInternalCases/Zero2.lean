import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero2
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalUpper
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero2 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourInternalUpper.K_zero2 => Physics.HiggsQuarticFourInternalUpper.K_zero2
]

assert_compatible GUT.HiggsQuarticFourInternalUpper.K_zero2 => Physics.HiggsQuarticFourInternalUpper.K_zero2
