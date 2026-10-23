import Physics.FieldTheory.Spinor.Weyl.WeylSpinor
import Physics.StandardModel.Gauge.SMEpsilonTensor
import Math.RepresentationTheory.ExternalInvariantTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylSpinor instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylSpinor.Group => Physics.WeylSpinor.Group,
  GUT.WeylSpinor.Space => Physics.WeylSpinor.Space,
  GUT.WeylSpinor.conjugate => Physics.WeylSpinor.conjugate,
  GUT.WeylSpinor.epsilonLeft => Physics.WeylSpinor.epsilonLeft,
  GUT.WeylSpinor.epsilonRight => Physics.WeylSpinor.epsilonRight,
  GUT.WeylSpinor.four => Physics.WeylSpinor.four,
  GUT.WeylSpinor.four_apply => Physics.WeylSpinor.four_apply,
  GUT.WeylSpinor.left => Physics.WeylSpinor.left,
  GUT.WeylSpinor.right => Physics.WeylSpinor.right,
  GUT.WeylSpinor.right_apply => Physics.WeylSpinor.right_apply
]

assert_compatible GUT.WeylSpinor.Group => Physics.WeylSpinor.Group
assert_compatible GUT.WeylSpinor.Space => Physics.WeylSpinor.Space
assert_compatible GUT.WeylSpinor.conjugate => Physics.WeylSpinor.conjugate
assert_compatible GUT.WeylSpinor.epsilonLeft => Physics.WeylSpinor.epsilonLeft
assert_compatible GUT.WeylSpinor.epsilonRight => Physics.WeylSpinor.epsilonRight
assert_compatible GUT.WeylSpinor.four => Physics.WeylSpinor.four
assert_compatible GUT.WeylSpinor.four_apply => Physics.WeylSpinor.four_apply
assert_compatible GUT.WeylSpinor.left => Physics.WeylSpinor.left
assert_compatible GUT.WeylSpinor.right => Physics.WeylSpinor.right
assert_compatible GUT.WeylSpinor.right_apply => Physics.WeylSpinor.right_apply
