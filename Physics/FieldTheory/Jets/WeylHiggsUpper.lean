import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsUpper
import Physics.FieldTheory.Jets.WeylHiggsEvenCoordinates
import Math.RepresentationTheory.SelectedRelationExtension
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsInternalLift.labels.eq_1 => Physics.WeylHiggsInternalLift.labels.eq_1,
  GUT.WeylHiggsUpper.bare_swap => Physics.WeylHiggsUpper.bare_swap,
  GUT.WeylHiggsUpper.evaluate_injective => Physics.WeylHiggsUpper.evaluate_injective,
  GUT.WeylHiggsUpper.even_zero => Physics.WeylHiggsUpper.even_zero,
  GUT.WeylHiggsUpper.instAddCommGroupA_physics => Physics.WeylHiggsUpper.instAddCommGroupA_physics,
  GUT.WeylHiggsUpper.instModuleComplexA_physics => Physics.WeylHiggsUpper.instModuleComplexA_physics,
  GUT.WeylHiggsUpper.instRingA_physics => Physics.WeylHiggsUpper.instRingA_physics,
  GUT.WeylHiggsUpper.left_coordinate_zero => Physics.WeylHiggsUpper.left_coordinate_zero,
  GUT.WeylHiggsUpper.left_even_zero => Physics.WeylHiggsUpper.left_even_zero,
  GUT.WeylHiggsUpper.selected_zero => Physics.WeylHiggsUpper.selected_zero,
  GUT.WeylHiggsUpper.swap_even => Physics.WeylHiggsUpper.swap_even,
  GUT.WeylHiggsUpper.whole_grade_zero => Physics.WeylHiggsUpper.whole_grade_zero
]

assert_compatible GUT.WeylHiggsInternalLift.labels.eq_1 => Physics.WeylHiggsInternalLift.labels.eq_1
assert_compatible GUT.WeylHiggsUpper.bare_swap => Physics.WeylHiggsUpper.bare_swap
assert_compatible GUT.WeylHiggsUpper.evaluate_injective => Physics.WeylHiggsUpper.evaluate_injective
assert_compatible GUT.WeylHiggsUpper.even_zero => Physics.WeylHiggsUpper.even_zero
assert_compatible GUT.WeylHiggsUpper.instAddCommGroupA_physics => Physics.WeylHiggsUpper.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsUpper.instModuleComplexA_physics => Physics.WeylHiggsUpper.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsUpper.instRingA_physics => Physics.WeylHiggsUpper.instRingA_physics
assert_compatible GUT.WeylHiggsUpper.left_coordinate_zero => Physics.WeylHiggsUpper.left_coordinate_zero
assert_compatible GUT.WeylHiggsUpper.left_even_zero => Physics.WeylHiggsUpper.left_even_zero
assert_compatible GUT.WeylHiggsUpper.selected_zero => Physics.WeylHiggsUpper.selected_zero
assert_compatible GUT.WeylHiggsUpper.swap_even => Physics.WeylHiggsUpper.swap_even
assert_compatible GUT.WeylHiggsUpper.whole_grade_zero => Physics.WeylHiggsUpper.whole_grade_zero
