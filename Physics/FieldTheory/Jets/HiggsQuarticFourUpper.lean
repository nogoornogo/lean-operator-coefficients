import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourUpper
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalComplete
import Physics.FieldTheory.Jets.HiggsQuarticFourLorentzUpper
import Math.RepresentationTheory.SelectedRelationExtension
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourUpper.evaluate_injective => Physics.HiggsQuarticFourUpper.evaluate_injective,
  GUT.HiggsQuarticFourUpper.internal_one => Physics.HiggsQuarticFourUpper.internal_one,
  GUT.HiggsQuarticFourUpper.internal_only => Physics.HiggsQuarticFourUpper.internal_only,
  GUT.HiggsQuarticFourUpper.lorentz_one => Physics.HiggsQuarticFourUpper.lorentz_one,
  GUT.HiggsQuarticFourUpper.lorentz_only => Physics.HiggsQuarticFourUpper.lorentz_only,
  GUT.HiggsQuarticFourUpper.selected_zero => Physics.HiggsQuarticFourUpper.selected_zero,
  GUT.HiggsQuarticFourUpper.whole_grade_zero => Physics.HiggsQuarticFourUpper.whole_grade_zero
]

assert_compatible GUT.HiggsQuarticFourUpper.evaluate_injective => Physics.HiggsQuarticFourUpper.evaluate_injective
assert_compatible GUT.HiggsQuarticFourUpper.internal_one => Physics.HiggsQuarticFourUpper.internal_one
assert_compatible GUT.HiggsQuarticFourUpper.internal_only => Physics.HiggsQuarticFourUpper.internal_only
assert_compatible GUT.HiggsQuarticFourUpper.lorentz_one => Physics.HiggsQuarticFourUpper.lorentz_one
assert_compatible GUT.HiggsQuarticFourUpper.lorentz_only => Physics.HiggsQuarticFourUpper.lorentz_only
assert_compatible GUT.HiggsQuarticFourUpper.selected_zero => Physics.HiggsQuarticFourUpper.selected_zero
assert_compatible GUT.HiggsQuarticFourUpper.whole_grade_zero => Physics.HiggsQuarticFourUpper.whole_grade_zero
