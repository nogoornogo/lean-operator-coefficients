import Physics.FieldTheory.Mass.Algebra.ProjectedWeylMass
import Physics.FieldTheory.Mass.SplitWeylMass
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.ProjectedWeylMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ProjectedWeylMass.Fields => Physics.ProjectedWeylMass.Fields,
  GUT.ProjectedWeylMass.form => Physics.ProjectedWeylMass.form,
  GUT.ProjectedWeylMass.form_apply => Physics.ProjectedWeylMass.form_apply,
  GUT.ProjectedWeylMass.form_eq_split => Physics.ProjectedWeylMass.form_eq_split,
  GUT.ProjectedWeylMass.mem_radical_of_projection => Physics.ProjectedWeylMass.mem_radical_of_projection,
  GUT.ProjectedWeylMass.projection => Physics.ProjectedWeylMass.projection,
  GUT.ProjectedWeylMass.projection_apply => Physics.ProjectedWeylMass.projection_apply
]

assert_compatible GUT.ProjectedWeylMass.Fields => Physics.ProjectedWeylMass.Fields
assert_compatible GUT.ProjectedWeylMass.form => Physics.ProjectedWeylMass.form
assert_compatible GUT.ProjectedWeylMass.form_apply => Physics.ProjectedWeylMass.form_apply
assert_compatible GUT.ProjectedWeylMass.form_eq_split => Physics.ProjectedWeylMass.form_eq_split
assert_compatible GUT.ProjectedWeylMass.mem_radical_of_projection => Physics.ProjectedWeylMass.mem_radical_of_projection
assert_compatible GUT.ProjectedWeylMass.projection => Physics.ProjectedWeylMass.projection
assert_compatible GUT.ProjectedWeylMass.projection_apply => Physics.ProjectedWeylMass.projection_apply
