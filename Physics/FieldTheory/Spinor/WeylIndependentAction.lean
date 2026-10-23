import Physics.FieldTheory.Spinor.Weyl.WeylIndependentAction
import Physics.FieldTheory.Spinor.WeylRealTransvections
import Math.RepresentationTheory.PairedPolynomialInvariants
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylIndependentAction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylIndependentAction.Group => Physics.WeylIndependentAction.Group,
  GUT.WeylIndependentAction.direction => Physics.WeylIndependentAction.direction,
  GUT.WeylIndependentAction.direction.eq_1 => Physics.WeylIndependentAction.direction.eq_1,
  GUT.WeylIndependentAction.family => Physics.WeylIndependentAction.family,
  GUT.WeylIndependentAction.family.eq_1 => Physics.WeylIndependentAction.family.eq_1,
  GUT.WeylIndependentAction.family_conjugate => Physics.WeylIndependentAction.family_conjugate,
  GUT.WeylIndependentAction.family_generates => Physics.WeylIndependentAction.family_generates,
  GUT.WeylIndependentAction.family_zero => Physics.WeylIndependentAction.family_zero,
  GUT.WeylIndependentAction.paired => Physics.WeylIndependentAction.paired,
  GUT.WeylIndependentAction.spin => Physics.WeylIndependentAction.spin,
  GUT.WeylIndependentAction.spin_affine => Physics.WeylIndependentAction.spin_affine,
  GUT.WeylIndependentAction.spin_paired => Physics.WeylIndependentAction.spin_paired
]

assert_compatible GUT.WeylIndependentAction.Group => Physics.WeylIndependentAction.Group
assert_compatible GUT.WeylIndependentAction.direction => Physics.WeylIndependentAction.direction
assert_compatible GUT.WeylIndependentAction.direction.eq_1 => Physics.WeylIndependentAction.direction.eq_1
assert_compatible GUT.WeylIndependentAction.family => Physics.WeylIndependentAction.family
assert_compatible GUT.WeylIndependentAction.family.eq_1 => Physics.WeylIndependentAction.family.eq_1
assert_compatible GUT.WeylIndependentAction.family_conjugate => Physics.WeylIndependentAction.family_conjugate
assert_compatible GUT.WeylIndependentAction.family_generates => Physics.WeylIndependentAction.family_generates
assert_compatible GUT.WeylIndependentAction.family_zero => Physics.WeylIndependentAction.family_zero
assert_compatible GUT.WeylIndependentAction.paired => Physics.WeylIndependentAction.paired
assert_compatible GUT.WeylIndependentAction.spin => Physics.WeylIndependentAction.spin
assert_compatible GUT.WeylIndependentAction.spin_affine => Physics.WeylIndependentAction.spin_affine
assert_compatible GUT.WeylIndependentAction.spin_paired => Physics.WeylIndependentAction.spin_paired
