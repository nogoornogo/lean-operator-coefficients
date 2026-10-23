import Physics.StandardModel.Operators.Support.Quark.SMColoredCubeBranching
import Physics.StandardModel.Operators.SMColoredCoreBranching
import Math.RepresentationTheory.SU3SpinExteriorCube
import Math.RepresentationTheory.SU3ConjugateSpinExteriorCube
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Quark.SMColoredCubeBranching instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMColoredCubeBranching.negativeCube => Physics.SMColoredCubeBranching.negativeCube,
  GUT.SMColoredCubeBranching.positiveCube => Physics.SMColoredCubeBranching.positiveCube
]

assert_compatible GUT.SMColoredCubeBranching.negativeCube => Physics.SMColoredCubeBranching.negativeCube
assert_compatible GUT.SMColoredCubeBranching.positiveCube => Physics.SMColoredCubeBranching.positiveCube
