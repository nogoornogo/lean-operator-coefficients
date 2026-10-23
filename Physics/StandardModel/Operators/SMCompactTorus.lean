import Physics.StandardModel.Operators.Support.Decomposition.SMCompactTorus
import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMCompactTorus instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMCompactTorus.Torus => Physics.SMCompactTorus.Torus,
  GUT.SMCompactTorus.Weight => Physics.SMCompactTorus.Weight,
  GUT.SMCompactTorus.alpha => Physics.SMCompactTorus.alpha,
  GUT.SMCompactTorus.beta => Physics.SMCompactTorus.beta,
  GUT.SMCompactTorus.color => Physics.SMCompactTorus.color,
  GUT.SMCompactTorus.colorEntries => Physics.SMCompactTorus.colorEntries,
  GUT.SMCompactTorus.colorEntries.eq_1 => Physics.SMCompactTorus.colorEntries.eq_1,
  GUT.SMCompactTorus.colorMatrix => Physics.SMCompactTorus.colorMatrix,
  GUT.SMCompactTorus.colorMatrix.eq_1 => Physics.SMCompactTorus.colorMatrix.eq_1,
  GUT.SMCompactTorus.color_continuous => Physics.SMCompactTorus.color_continuous,
  GUT.SMCompactTorus.color_mem => Physics.SMCompactTorus.color_mem,
  GUT.SMCompactTorus.inclusion => Physics.SMCompactTorus.inclusion,
  GUT.SMCompactTorus.leftRoot => Physics.SMCompactTorus.leftRoot,
  GUT.SMCompactTorus.monomial => Physics.SMCompactTorus.monomial,
  GUT.SMCompactTorus.rightRoot => Physics.SMCompactTorus.rightRoot,
  GUT.SMCompactTorus.roots => Physics.SMCompactTorus.roots,
  GUT.SMCompactTorus.weakRoot => Physics.SMCompactTorus.weakRoot
]

assert_compatible GUT.SMCompactTorus.Torus => Physics.SMCompactTorus.Torus
assert_compatible GUT.SMCompactTorus.Weight => Physics.SMCompactTorus.Weight
assert_compatible GUT.SMCompactTorus.alpha => Physics.SMCompactTorus.alpha
assert_compatible GUT.SMCompactTorus.beta => Physics.SMCompactTorus.beta
assert_compatible GUT.SMCompactTorus.color => Physics.SMCompactTorus.color
assert_compatible GUT.SMCompactTorus.colorEntries => Physics.SMCompactTorus.colorEntries
assert_compatible GUT.SMCompactTorus.colorEntries.eq_1 => Physics.SMCompactTorus.colorEntries.eq_1
assert_compatible GUT.SMCompactTorus.colorMatrix => Physics.SMCompactTorus.colorMatrix
assert_compatible GUT.SMCompactTorus.colorMatrix.eq_1 => Physics.SMCompactTorus.colorMatrix.eq_1
assert_compatible GUT.SMCompactTorus.color_continuous => Physics.SMCompactTorus.color_continuous
assert_compatible GUT.SMCompactTorus.color_mem => Physics.SMCompactTorus.color_mem
assert_compatible GUT.SMCompactTorus.inclusion => Physics.SMCompactTorus.inclusion
assert_compatible GUT.SMCompactTorus.leftRoot => Physics.SMCompactTorus.leftRoot
assert_compatible GUT.SMCompactTorus.monomial => Physics.SMCompactTorus.monomial
assert_compatible GUT.SMCompactTorus.rightRoot => Physics.SMCompactTorus.rightRoot
assert_compatible GUT.SMCompactTorus.roots => Physics.SMCompactTorus.roots
assert_compatible GUT.SMCompactTorus.weakRoot => Physics.SMCompactTorus.weakRoot
