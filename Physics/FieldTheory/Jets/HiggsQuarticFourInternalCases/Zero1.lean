import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero1
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalUpper
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Core.Zero1 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourInternalUpper.K_zero1 => Physics.HiggsQuarticFourInternalUpper.K_zero1
]

assert_compatible GUT.HiggsQuarticFourInternalUpper.K_zero1 => Physics.HiggsQuarticFourInternalUpper.K_zero1
