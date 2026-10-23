import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalComplete
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Zero0
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Zero1
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Zero2
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalCases.Zero3
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalComplete instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourInternalUpper.K_zero => Physics.HiggsQuarticFourInternalUpper.K_zero,
  GUT.HiggsQuarticFourInternalUpper.all_pairs_zero => Physics.HiggsQuarticFourInternalUpper.all_pairs_zero
]

assert_compatible GUT.HiggsQuarticFourInternalUpper.K_zero => Physics.HiggsQuarticFourInternalUpper.K_zero
assert_compatible GUT.HiggsQuarticFourInternalUpper.all_pairs_zero => Physics.HiggsQuarticFourInternalUpper.all_pairs_zero
