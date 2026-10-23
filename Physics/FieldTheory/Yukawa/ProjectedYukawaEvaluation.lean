import Physics.FieldTheory.Yukawa.Mass.ProjectedYukawaEvaluation
import Physics.FieldTheory.Yukawa.ProjectedYukawa
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.ProjectedYukawaEvaluation instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ProjectedYukawa.combine_apply => Physics.ProjectedYukawa.combine_apply,
  GUT.ProjectedYukawa.diagonal_apply => Physics.ProjectedYukawa.diagonal_apply,
  GUT.ProjectedYukawa.fiveFamily => Physics.ProjectedYukawa.fiveFamily,
  GUT.ProjectedYukawa.fiveFamily.eq_1 => Physics.ProjectedYukawa.fiveFamily.eq_1,
  GUT.ProjectedYukawa.fiveFamily_form => Physics.ProjectedYukawa.fiveFamily_form,
  GUT.ProjectedYukawa.fiveForm => Physics.ProjectedYukawa.fiveForm,
  GUT.ProjectedYukawa.fiveForm.eq_1 => Physics.ProjectedYukawa.fiveForm.eq_1,
  GUT.ProjectedYukawa.fiveForm_coordinates => Physics.ProjectedYukawa.fiveForm_coordinates,
  GUT.ProjectedYukawa.fiveForm_flavor_coordinates => Physics.ProjectedYukawa.fiveForm_flavor_coordinates,
  GUT.ProjectedYukawa.flavorLinear => Physics.ProjectedYukawa.flavorLinear,
  GUT.ProjectedYukawa.flavorLinear.eq_1 => Physics.ProjectedYukawa.flavorLinear.eq_1,
  GUT.ProjectedYukawa.mixed_apply => Physics.ProjectedYukawa.mixed_apply,
  GUT.ProjectedYukawa.zeroBare_form => Physics.ProjectedYukawa.zeroBare_form
]

assert_compatible GUT.ProjectedYukawa.combine_apply => Physics.ProjectedYukawa.combine_apply
assert_compatible GUT.ProjectedYukawa.diagonal_apply => Physics.ProjectedYukawa.diagonal_apply
assert_compatible GUT.ProjectedYukawa.fiveFamily => Physics.ProjectedYukawa.fiveFamily
assert_compatible GUT.ProjectedYukawa.fiveFamily.eq_1 => Physics.ProjectedYukawa.fiveFamily.eq_1
assert_compatible GUT.ProjectedYukawa.fiveFamily_form => Physics.ProjectedYukawa.fiveFamily_form
assert_compatible GUT.ProjectedYukawa.fiveForm => Physics.ProjectedYukawa.fiveForm
assert_compatible GUT.ProjectedYukawa.fiveForm.eq_1 => Physics.ProjectedYukawa.fiveForm.eq_1
assert_compatible GUT.ProjectedYukawa.fiveForm_coordinates => Physics.ProjectedYukawa.fiveForm_coordinates
assert_compatible GUT.ProjectedYukawa.fiveForm_flavor_coordinates => Physics.ProjectedYukawa.fiveForm_flavor_coordinates
assert_compatible GUT.ProjectedYukawa.flavorLinear => Physics.ProjectedYukawa.flavorLinear
assert_compatible GUT.ProjectedYukawa.flavorLinear.eq_1 => Physics.ProjectedYukawa.flavorLinear.eq_1
assert_compatible GUT.ProjectedYukawa.mixed_apply => Physics.ProjectedYukawa.mixed_apply
assert_compatible GUT.ProjectedYukawa.zeroBare_form => Physics.ProjectedYukawa.zeroBare_form
