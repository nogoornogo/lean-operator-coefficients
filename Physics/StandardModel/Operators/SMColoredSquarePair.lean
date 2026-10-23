import Physics.StandardModel.Operators.Support.Quark.SMColoredSquarePair
import Physics.StandardModel.Operators.SMColoredCoreBranching
import Math.RepresentationTheory.SpinSquarePairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMColoredSquarePair instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMColoredSquarePair.allowed => Physics.SMColoredSquarePair.allowed,
  GUT.SMColoredSquarePair.color => Physics.SMColoredSquarePair.color,
  GUT.SMColoredSquarePair.instAddCommGroupTensorProductComplex_physics => Physics.SMColoredSquarePair.instAddCommGroupTensorProductComplex_physics,
  GUT.SMColoredSquarePair.left => Physics.SMColoredSquarePair.left,
  GUT.SMColoredSquarePair.leftTop => Physics.SMColoredSquarePair.leftTop,
  GUT.SMColoredSquarePair.right => Physics.SMColoredSquarePair.right,
  GUT.SMColoredSquarePair.rightTop => Physics.SMColoredSquarePair.rightTop
]

assert_compatible GUT.SMColoredSquarePair.allowed => Physics.SMColoredSquarePair.allowed
assert_compatible GUT.SMColoredSquarePair.color => Physics.SMColoredSquarePair.color
assert_compatible GUT.SMColoredSquarePair.instAddCommGroupTensorProductComplex_physics => Physics.SMColoredSquarePair.instAddCommGroupTensorProductComplex_physics
assert_compatible GUT.SMColoredSquarePair.left => Physics.SMColoredSquarePair.left
assert_compatible GUT.SMColoredSquarePair.leftTop => Physics.SMColoredSquarePair.leftTop
assert_compatible GUT.SMColoredSquarePair.right => Physics.SMColoredSquarePair.right
assert_compatible GUT.SMColoredSquarePair.rightTop => Physics.SMColoredSquarePair.rightTop
