import Physics.FieldTheory.Yukawa.Mass.ProjectedYukawa
import Physics.FieldTheory.Yukawa.WeylYukawaMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.ProjectedYukawa instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ProjectedYukawa.combine => Physics.ProjectedYukawa.combine,
  GUT.ProjectedYukawa.diagonal => Physics.ProjectedYukawa.diagonal,
  GUT.ProjectedYukawa.evaluated_combination => Physics.ProjectedYukawa.evaluated_combination,
  GUT.ProjectedYukawa.family => Physics.ProjectedYukawa.family,
  GUT.ProjectedYukawa.familyMass => Physics.ProjectedYukawa.familyMass,
  GUT.ProjectedYukawa.familyMass_congr => Physics.ProjectedYukawa.familyMass_congr,
  GUT.ProjectedYukawa.familyMass_form => Physics.ProjectedYukawa.familyMass_form,
  GUT.ProjectedYukawa.generated_mass_eq_from_form => Physics.ProjectedYukawa.generated_mass_eq_from_form,
  GUT.ProjectedYukawa.mixed => Physics.ProjectedYukawa.mixed,
  GUT.ProjectedYukawa.projectedForm => Physics.ProjectedYukawa.projectedForm
]

assert_compatible GUT.ProjectedYukawa.combine => Physics.ProjectedYukawa.combine
assert_compatible GUT.ProjectedYukawa.diagonal => Physics.ProjectedYukawa.diagonal
assert_compatible GUT.ProjectedYukawa.evaluated_combination => Physics.ProjectedYukawa.evaluated_combination
assert_compatible GUT.ProjectedYukawa.family => Physics.ProjectedYukawa.family
assert_compatible GUT.ProjectedYukawa.familyMass => Physics.ProjectedYukawa.familyMass
assert_compatible GUT.ProjectedYukawa.familyMass_congr => Physics.ProjectedYukawa.familyMass_congr
assert_compatible GUT.ProjectedYukawa.familyMass_form => Physics.ProjectedYukawa.familyMass_form
assert_compatible GUT.ProjectedYukawa.generated_mass_eq_from_form => Physics.ProjectedYukawa.generated_mass_eq_from_form
assert_compatible GUT.ProjectedYukawa.mixed => Physics.ProjectedYukawa.mixed
assert_compatible GUT.ProjectedYukawa.projectedForm => Physics.ProjectedYukawa.projectedForm
