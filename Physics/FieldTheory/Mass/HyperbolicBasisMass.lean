import Physics.FieldTheory.Mass.Algebra.HyperbolicBasisMass
import Physics.FieldTheory.Mass.InvariantWeylMass
import Math.LinearAlgebra.EigenbasisTrace
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.HyperbolicBasisMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HyperbolicBasisMass.Index => Physics.HyperbolicBasisMass.Index,
  GUT.HyperbolicBasisMass.coord_action => Physics.HyperbolicBasisMass.coord_action,
  GUT.HyperbolicBasisMass.form => Physics.HyperbolicBasisMass.form,
  GUT.HyperbolicBasisMass.form.eq_1 => Physics.HyperbolicBasisMass.form.eq_1,
  GUT.HyperbolicBasisMass.form_apply => Physics.HyperbolicBasisMass.form_apply,
  GUT.HyperbolicBasisMass.form_ne_zero => Physics.HyperbolicBasisMass.form_ne_zero,
  GUT.HyperbolicBasisMass.form_pair => Physics.HyperbolicBasisMass.form_pair,
  GUT.HyperbolicBasisMass.form_symmetric => Physics.HyperbolicBasisMass.form_symmetric,
  GUT.HyperbolicBasisMass.lightBasis => Physics.HyperbolicBasisMass.lightBasis,
  GUT.HyperbolicBasisMass.lightBasis.eq_1 => Physics.HyperbolicBasisMass.lightBasis.eq_1,
  GUT.HyperbolicBasisMass.lightBasis_action => Physics.HyperbolicBasisMass.lightBasis_action,
  GUT.HyperbolicBasisMass.lightCoordinates => Physics.HyperbolicBasisMass.lightCoordinates,
  GUT.HyperbolicBasisMass.lightCoordinates_bijective => Physics.HyperbolicBasisMass.lightCoordinates_bijective,
  GUT.HyperbolicBasisMass.lightEquiv => Physics.HyperbolicBasisMass.lightEquiv,
  GUT.HyperbolicBasisMass.mass => Physics.HyperbolicBasisMass.mass,
  GUT.HyperbolicBasisMass.mem_radical_iff => Physics.HyperbolicBasisMass.mem_radical_iff,
  GUT.HyperbolicBasisMass.radical_character => Physics.HyperbolicBasisMass.radical_character,
  GUT.HyperbolicBasisMass.radical_finrank => Physics.HyperbolicBasisMass.radical_finrank
]

assert_compatible GUT.HyperbolicBasisMass.Index => Physics.HyperbolicBasisMass.Index
assert_compatible GUT.HyperbolicBasisMass.coord_action => Physics.HyperbolicBasisMass.coord_action
assert_compatible GUT.HyperbolicBasisMass.form => Physics.HyperbolicBasisMass.form
assert_compatible GUT.HyperbolicBasisMass.form.eq_1 => Physics.HyperbolicBasisMass.form.eq_1
assert_compatible GUT.HyperbolicBasisMass.form_apply => Physics.HyperbolicBasisMass.form_apply
assert_compatible GUT.HyperbolicBasisMass.form_ne_zero => Physics.HyperbolicBasisMass.form_ne_zero
assert_compatible GUT.HyperbolicBasisMass.form_pair => Physics.HyperbolicBasisMass.form_pair
assert_compatible GUT.HyperbolicBasisMass.form_symmetric => Physics.HyperbolicBasisMass.form_symmetric
assert_compatible GUT.HyperbolicBasisMass.lightBasis => Physics.HyperbolicBasisMass.lightBasis
assert_compatible GUT.HyperbolicBasisMass.lightBasis.eq_1 => Physics.HyperbolicBasisMass.lightBasis.eq_1
assert_compatible GUT.HyperbolicBasisMass.lightBasis_action => Physics.HyperbolicBasisMass.lightBasis_action
assert_compatible GUT.HyperbolicBasisMass.lightCoordinates => Physics.HyperbolicBasisMass.lightCoordinates
assert_compatible GUT.HyperbolicBasisMass.lightCoordinates_bijective => Physics.HyperbolicBasisMass.lightCoordinates_bijective
assert_compatible GUT.HyperbolicBasisMass.lightEquiv => Physics.HyperbolicBasisMass.lightEquiv
assert_compatible GUT.HyperbolicBasisMass.mass => Physics.HyperbolicBasisMass.mass
assert_compatible GUT.HyperbolicBasisMass.mem_radical_iff => Physics.HyperbolicBasisMass.mem_radical_iff
assert_compatible GUT.HyperbolicBasisMass.radical_character => Physics.HyperbolicBasisMass.radical_character
assert_compatible GUT.HyperbolicBasisMass.radical_finrank => Physics.HyperbolicBasisMass.radical_finrank
