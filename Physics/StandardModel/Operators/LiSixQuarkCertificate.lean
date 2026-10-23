import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkCertificate
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.LiSixQuarkOrbitData
import Physics.StandardModel.Operators.LiSixQuarkBlockExtraction
import Physics.StandardModel.Operators.LiSixQuarkReducedSeeds
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkCertificate.assemble_extract => Physics.LiSixQuarkCertificate.assemble_extract,
  GUT.LiSixQuarkCertificate.basisMatrix => Physics.LiSixQuarkCertificate.basisMatrix,
  GUT.LiSixQuarkCertificate.colorMatrixR.eq_1 => Physics.LiSixQuarkCertificate.colorMatrixR.eq_1,
  GUT.LiSixQuarkCertificate.colorMatrixR_cast => Physics.LiSixQuarkCertificate.colorMatrixR_cast,
  GUT.LiSixQuarkCertificate.coordinateEquiv => Physics.LiSixQuarkCertificate.coordinateEquiv,
  GUT.LiSixQuarkCertificate.extra_outside_printed_span => Physics.LiSixQuarkCertificate.extra_outside_printed_span,
  GUT.LiSixQuarkCertificate.extract_assemble => Physics.LiSixQuarkCertificate.extract_assemble,
  GUT.LiSixQuarkCertificate.flatten => Physics.LiSixQuarkCertificate.flatten,
  GUT.LiSixQuarkCertificate.inverseMatrix => Physics.LiSixQuarkCertificate.inverseMatrix,
  GUT.LiSixQuarkCertificate.inverseMatrix.eq_1 => Physics.LiSixQuarkCertificate.inverseMatrix.eq_1,
  GUT.LiSixQuarkCertificate.left_inverse => Physics.LiSixQuarkCertificate.left_inverse,
  GUT.LiSixQuarkCertificate.matrixEquiv => Physics.LiSixQuarkCertificate.matrixEquiv,
  GUT.LiSixQuarkCertificate.orbitArray => Physics.LiSixQuarkCertificate.orbitArray,
  GUT.LiSixQuarkCertificate.orbitArray_agrees => Physics.LiSixQuarkCertificate.orbitArray_agrees,
  GUT.LiSixQuarkCertificate.printed_orbit_probe_zero => Physics.LiSixQuarkCertificate.printed_orbit_probe_zero,
  GUT.LiSixQuarkCertificate.printed_probe_zero => Physics.LiSixQuarkCertificate.printed_probe_zero,
  GUT.LiSixQuarkCertificate.right_inverse => Physics.LiSixQuarkCertificate.right_inverse,
  GUT.LiSixQuarkCertificate.spinMatrixR.eq_1 => Physics.LiSixQuarkCertificate.spinMatrixR.eq_1,
  GUT.LiSixQuarkCertificate.spinMatrixR_cast => Physics.LiSixQuarkCertificate.spinMatrixR_cast,
  GUT.LiSixQuarkCertificate.transformR_cast => Physics.LiSixQuarkCertificate.transformR_cast,
  GUT.LiSixQuarkCertificate.wordR_cast => Physics.LiSixQuarkCertificate.wordR_cast
]

assert_compatible GUT.LiSixQuarkCertificate.assemble_extract => Physics.LiSixQuarkCertificate.assemble_extract
assert_compatible GUT.LiSixQuarkCertificate.basisMatrix => Physics.LiSixQuarkCertificate.basisMatrix
assert_compatible GUT.LiSixQuarkCertificate.colorMatrixR.eq_1 => Physics.LiSixQuarkCertificate.colorMatrixR.eq_1
assert_compatible GUT.LiSixQuarkCertificate.colorMatrixR_cast => Physics.LiSixQuarkCertificate.colorMatrixR_cast
assert_compatible GUT.LiSixQuarkCertificate.coordinateEquiv => Physics.LiSixQuarkCertificate.coordinateEquiv
assert_compatible GUT.LiSixQuarkCertificate.extra_outside_printed_span => Physics.LiSixQuarkCertificate.extra_outside_printed_span
assert_compatible GUT.LiSixQuarkCertificate.extract_assemble => Physics.LiSixQuarkCertificate.extract_assemble
assert_compatible GUT.LiSixQuarkCertificate.flatten => Physics.LiSixQuarkCertificate.flatten
assert_compatible GUT.LiSixQuarkCertificate.inverseMatrix => Physics.LiSixQuarkCertificate.inverseMatrix
assert_compatible GUT.LiSixQuarkCertificate.inverseMatrix.eq_1 => Physics.LiSixQuarkCertificate.inverseMatrix.eq_1
assert_compatible GUT.LiSixQuarkCertificate.left_inverse => Physics.LiSixQuarkCertificate.left_inverse
assert_compatible GUT.LiSixQuarkCertificate.matrixEquiv => Physics.LiSixQuarkCertificate.matrixEquiv
assert_compatible GUT.LiSixQuarkCertificate.orbitArray => Physics.LiSixQuarkCertificate.orbitArray
assert_compatible GUT.LiSixQuarkCertificate.orbitArray_agrees => Physics.LiSixQuarkCertificate.orbitArray_agrees
assert_compatible GUT.LiSixQuarkCertificate.printed_orbit_probe_zero => Physics.LiSixQuarkCertificate.printed_orbit_probe_zero
assert_compatible GUT.LiSixQuarkCertificate.printed_probe_zero => Physics.LiSixQuarkCertificate.printed_probe_zero
assert_compatible GUT.LiSixQuarkCertificate.right_inverse => Physics.LiSixQuarkCertificate.right_inverse
assert_compatible GUT.LiSixQuarkCertificate.spinMatrixR.eq_1 => Physics.LiSixQuarkCertificate.spinMatrixR.eq_1
assert_compatible GUT.LiSixQuarkCertificate.spinMatrixR_cast => Physics.LiSixQuarkCertificate.spinMatrixR_cast
assert_compatible GUT.LiSixQuarkCertificate.transformR_cast => Physics.LiSixQuarkCertificate.transformR_cast
assert_compatible GUT.LiSixQuarkCertificate.wordR_cast => Physics.LiSixQuarkCertificate.wordR_cast
