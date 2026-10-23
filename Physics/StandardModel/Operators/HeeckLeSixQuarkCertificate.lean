import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkCertificate
import Physics.StandardModel.Operators.HeeckLeSixQuarkConvention
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkCertificate.assemble_extract => Physics.HeeckLeSixQuarkCertificate.assemble_extract,
  GUT.HeeckLeSixQuarkCertificate.basisMatrix => Physics.HeeckLeSixQuarkCertificate.basisMatrix,
  GUT.HeeckLeSixQuarkCertificate.basisMatrix.eq_1 => Physics.HeeckLeSixQuarkCertificate.basisMatrix.eq_1,
  GUT.HeeckLeSixQuarkCertificate.coordinateEquiv => Physics.HeeckLeSixQuarkCertificate.coordinateEquiv,
  GUT.HeeckLeSixQuarkCertificate.extract_assemble => Physics.HeeckLeSixQuarkCertificate.extract_assemble,
  GUT.HeeckLeSixQuarkCertificate.flatten => Physics.HeeckLeSixQuarkCertificate.flatten,
  GUT.HeeckLeSixQuarkCertificate.inverseMatrix => Physics.HeeckLeSixQuarkCertificate.inverseMatrix,
  GUT.HeeckLeSixQuarkCertificate.inverseMatrix.eq_1 => Physics.HeeckLeSixQuarkCertificate.inverseMatrix.eq_1,
  GUT.HeeckLeSixQuarkCertificate.left_inverse => Physics.HeeckLeSixQuarkCertificate.left_inverse,
  GUT.HeeckLeSixQuarkCertificate.matrixEquiv => Physics.HeeckLeSixQuarkCertificate.matrixEquiv,
  GUT.HeeckLeSixQuarkCertificate.orbitArray_agrees => Physics.HeeckLeSixQuarkCertificate.orbitArray_agrees,
  GUT.HeeckLeSixQuarkCertificate.right_inverse => Physics.HeeckLeSixQuarkCertificate.right_inverse
]

assert_compatible GUT.HeeckLeSixQuarkCertificate.assemble_extract => Physics.HeeckLeSixQuarkCertificate.assemble_extract
assert_compatible GUT.HeeckLeSixQuarkCertificate.basisMatrix => Physics.HeeckLeSixQuarkCertificate.basisMatrix
assert_compatible GUT.HeeckLeSixQuarkCertificate.basisMatrix.eq_1 => Physics.HeeckLeSixQuarkCertificate.basisMatrix.eq_1
assert_compatible GUT.HeeckLeSixQuarkCertificate.coordinateEquiv => Physics.HeeckLeSixQuarkCertificate.coordinateEquiv
assert_compatible GUT.HeeckLeSixQuarkCertificate.extract_assemble => Physics.HeeckLeSixQuarkCertificate.extract_assemble
assert_compatible GUT.HeeckLeSixQuarkCertificate.flatten => Physics.HeeckLeSixQuarkCertificate.flatten
assert_compatible GUT.HeeckLeSixQuarkCertificate.inverseMatrix => Physics.HeeckLeSixQuarkCertificate.inverseMatrix
assert_compatible GUT.HeeckLeSixQuarkCertificate.inverseMatrix.eq_1 => Physics.HeeckLeSixQuarkCertificate.inverseMatrix.eq_1
assert_compatible GUT.HeeckLeSixQuarkCertificate.left_inverse => Physics.HeeckLeSixQuarkCertificate.left_inverse
assert_compatible GUT.HeeckLeSixQuarkCertificate.matrixEquiv => Physics.HeeckLeSixQuarkCertificate.matrixEquiv
assert_compatible GUT.HeeckLeSixQuarkCertificate.orbitArray_agrees => Physics.HeeckLeSixQuarkCertificate.orbitArray_agrees
assert_compatible GUT.HeeckLeSixQuarkCertificate.right_inverse => Physics.HeeckLeSixQuarkCertificate.right_inverse
