import Physics.FieldTheory.Mass.Algebra.InvariantLineMass
import Physics.FieldTheory.Mass.InvariantWeylMass
import Physics.FieldTheory.Mass.UnitaryVirtualRealization
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.InvariantLineMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InvariantLineMass.form => Physics.InvariantLineMass.form,
  GUT.InvariantLineMass.form_apply => Physics.InvariantLineMass.form_apply,
  GUT.InvariantLineMass.form_ne_zero => Physics.InvariantLineMass.form_ne_zero,
  GUT.InvariantLineMass.mass => Physics.InvariantLineMass.mass,
  GUT.InvariantLineMass.radical_eq_ker => Physics.InvariantLineMass.radical_eq_ker,
  GUT.InvariantLineMass.radical_finrank_add_one => Physics.InvariantLineMass.radical_finrank_add_one
]

assert_compatible GUT.InvariantLineMass.form => Physics.InvariantLineMass.form
assert_compatible GUT.InvariantLineMass.form_apply => Physics.InvariantLineMass.form_apply
assert_compatible GUT.InvariantLineMass.form_ne_zero => Physics.InvariantLineMass.form_ne_zero
assert_compatible GUT.InvariantLineMass.mass => Physics.InvariantLineMass.mass
assert_compatible GUT.InvariantLineMass.radical_eq_ker => Physics.InvariantLineMass.radical_eq_ker
assert_compatible GUT.InvariantLineMass.radical_finrank_add_one => Physics.InvariantLineMass.radical_finrank_add_one
