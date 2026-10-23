import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkMatrix
import Physics.StandardModel.Operators.HeeckLeSixQuarkExtraction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkMatrix instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkMatrix.basis => Physics.HeeckLeSixQuarkMatrix.basis,
  GUT.HeeckLeSixQuarkMatrix.basis.eq_1 => Physics.HeeckLeSixQuarkMatrix.basis.eq_1,
  GUT.HeeckLeSixQuarkMatrix.flatten => Physics.HeeckLeSixQuarkMatrix.flatten,
  GUT.HeeckLeSixQuarkMatrix.forward_mulVec => Physics.HeeckLeSixQuarkMatrix.forward_mulVec,
  GUT.HeeckLeSixQuarkMatrix.inverse => Physics.HeeckLeSixQuarkMatrix.inverse,
  GUT.HeeckLeSixQuarkMatrix.inverse.congr_simp => Physics.HeeckLeSixQuarkMatrix.inverse.congr_simp,
  GUT.HeeckLeSixQuarkMatrix.inverse.eq_1 => Physics.HeeckLeSixQuarkMatrix.inverse.eq_1,
  GUT.HeeckLeSixQuarkMatrix.left_inverse => Physics.HeeckLeSixQuarkMatrix.left_inverse,
  GUT.HeeckLeSixQuarkMatrix.right_inverse => Physics.HeeckLeSixQuarkMatrix.right_inverse
]

assert_compatible GUT.HeeckLeSixQuarkMatrix.basis => Physics.HeeckLeSixQuarkMatrix.basis
assert_compatible GUT.HeeckLeSixQuarkMatrix.basis.eq_1 => Physics.HeeckLeSixQuarkMatrix.basis.eq_1
assert_compatible GUT.HeeckLeSixQuarkMatrix.flatten => Physics.HeeckLeSixQuarkMatrix.flatten
assert_compatible GUT.HeeckLeSixQuarkMatrix.forward_mulVec => Physics.HeeckLeSixQuarkMatrix.forward_mulVec
assert_compatible GUT.HeeckLeSixQuarkMatrix.inverse => Physics.HeeckLeSixQuarkMatrix.inverse
assert_compatible GUT.HeeckLeSixQuarkMatrix.inverse.congr_simp => Physics.HeeckLeSixQuarkMatrix.inverse.congr_simp
assert_compatible GUT.HeeckLeSixQuarkMatrix.inverse.eq_1 => Physics.HeeckLeSixQuarkMatrix.inverse.eq_1
assert_compatible GUT.HeeckLeSixQuarkMatrix.left_inverse => Physics.HeeckLeSixQuarkMatrix.left_inverse
assert_compatible GUT.HeeckLeSixQuarkMatrix.right_inverse => Physics.HeeckLeSixQuarkMatrix.right_inverse
