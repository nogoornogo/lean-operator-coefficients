import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiInput
import Physics.FieldTheory.Jets.HiggsQuarticFourLiRelations
import Math.RepresentationTheory.SelectedRelationExtension
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLiInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourLiInput.box_grade => Physics.HiggsQuarticFourLiInput.box_grade,
  GUT.HiggsQuarticFourLiInput.coefficient_values => Physics.HiggsQuarticFourLiInput.coefficient_values,
  GUT.HiggsQuarticFourLiInput.coordinate => Physics.HiggsQuarticFourLiInput.coordinate,
  GUT.HiggsQuarticFourLiInput.l1_grade => Physics.HiggsQuarticFourLiInput.l1_grade,
  GUT.HiggsQuarticFourLiInput.l2_grade => Physics.HiggsQuarticFourLiInput.l2_grade,
  GUT.HiggsQuarticFourLiInput.l3_grade => Physics.HiggsQuarticFourLiInput.l3_grade,
  GUT.HiggsQuarticFourLiInput.left_grade => Physics.HiggsQuarticFourLiInput.left_grade,
  GUT.HiggsQuarticFourLiInput.native => Physics.HiggsQuarticFourLiInput.native,
  GUT.HiggsQuarticFourLiInput.rho_grade => Physics.HiggsQuarticFourLiInput.rho_grade,
  GUT.HiggsQuarticFourLiInput.right_grade => Physics.HiggsQuarticFourLiInput.right_grade,
  GUT.HiggsQuarticFourLiInput.secondDual_grade => Physics.HiggsQuarticFourLiInput.secondDual_grade,
  GUT.HiggsQuarticFourLiInput.second_grade => Physics.HiggsQuarticFourLiInput.second_grade
]

assert_compatible GUT.HiggsQuarticFourLiInput.box_grade => Physics.HiggsQuarticFourLiInput.box_grade
assert_compatible GUT.HiggsQuarticFourLiInput.coefficient_values => Physics.HiggsQuarticFourLiInput.coefficient_values
assert_compatible GUT.HiggsQuarticFourLiInput.coordinate => Physics.HiggsQuarticFourLiInput.coordinate
assert_compatible GUT.HiggsQuarticFourLiInput.l1_grade => Physics.HiggsQuarticFourLiInput.l1_grade
assert_compatible GUT.HiggsQuarticFourLiInput.l2_grade => Physics.HiggsQuarticFourLiInput.l2_grade
assert_compatible GUT.HiggsQuarticFourLiInput.l3_grade => Physics.HiggsQuarticFourLiInput.l3_grade
assert_compatible GUT.HiggsQuarticFourLiInput.left_grade => Physics.HiggsQuarticFourLiInput.left_grade
assert_compatible GUT.HiggsQuarticFourLiInput.native => Physics.HiggsQuarticFourLiInput.native
assert_compatible GUT.HiggsQuarticFourLiInput.rho_grade => Physics.HiggsQuarticFourLiInput.rho_grade
assert_compatible GUT.HiggsQuarticFourLiInput.right_grade => Physics.HiggsQuarticFourLiInput.right_grade
assert_compatible GUT.HiggsQuarticFourLiInput.secondDual_grade => Physics.HiggsQuarticFourLiInput.secondDual_grade
assert_compatible GUT.HiggsQuarticFourLiInput.second_grade => Physics.HiggsQuarticFourLiInput.second_grade
