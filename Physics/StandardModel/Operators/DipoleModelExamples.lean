import Physics.StandardModel.Operators.Dipole.DipoleModelExamples
import Physics.StandardModel.Operators.DipoleMatrixInterface
import Physics.StandardModel.Operators.DipoleCouplingControls
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleModelExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleControls.generation.eq_1 => Physics.DipoleControls.generation.eq_1,
  GUT.DipoleMatrixInterface.register.congr_simp => Physics.DipoleMatrixInterface.register.congr_simp,
  GUT.DipoleModelExamples.cancelling => Physics.DipoleModelExamples.cancelling,
  GUT.DipoleModelExamples.cancelling.eq_1 => Physics.DipoleModelExamples.cancelling.eq_1,
  GUT.DipoleModelExamples.cancellingCertificate => Physics.DipoleModelExamples.cancellingCertificate,
  GUT.DipoleModelExamples.cancellingCertificate.eq_1 => Physics.DipoleModelExamples.cancellingCertificate.eq_1,
  GUT.DipoleModelExamples.cancellingPaths => Physics.DipoleModelExamples.cancellingPaths,
  GUT.DipoleModelExamples.cancellingPaths.eq_1 => Physics.DipoleModelExamples.cancellingPaths.eq_1,
  GUT.DipoleModelExamples.cancelling_no_nonzero => Physics.DipoleModelExamples.cancelling_no_nonzero,
  GUT.DipoleModelExamples.correlated => Physics.DipoleModelExamples.correlated,
  GUT.DipoleModelExamples.correlated_nonzero_iff => Physics.DipoleModelExamples.correlated_nonzero_iff,
  GUT.DipoleModelExamples.correlated_selected => Physics.DipoleModelExamples.correlated_selected,
  GUT.DipoleModelExamples.cubic => Physics.DipoleModelExamples.cubic,
  GUT.DipoleModelExamples.cubic.eq_1 => Physics.DipoleModelExamples.cubic.eq_1,
  GUT.DipoleModelExamples.cubicCertificate => Physics.DipoleModelExamples.cubicCertificate,
  GUT.DipoleModelExamples.cubicCertificate.eq_1 => Physics.DipoleModelExamples.cubicCertificate.eq_1,
  GUT.DipoleModelExamples.cubicPaths => Physics.DipoleModelExamples.cubicPaths,
  GUT.DipoleModelExamples.cubicPaths.eq_1 => Physics.DipoleModelExamples.cubicPaths.eq_1,
  GUT.DipoleModelExamples.cubicWeights => Physics.DipoleModelExamples.cubicWeights,
  GUT.DipoleModelExamples.cubicWeights.eq_1 => Physics.DipoleModelExamples.cubicWeights.eq_1,
  GUT.DipoleModelExamples.cubic_realized => Physics.DipoleModelExamples.cubic_realized,
  GUT.DipoleModelExamples.externalModel => Physics.DipoleModelExamples.externalModel,
  GUT.DipoleModelExamples.external_nonzero_iff => Physics.DipoleModelExamples.external_nonzero_iff,
  GUT.DipoleModelExamples.matrices => Physics.DipoleModelExamples.matrices,
  GUT.DipoleModelExamples.matrices.eq_1 => Physics.DipoleModelExamples.matrices.eq_1,
  GUT.DipoleModelExamples.matrixModel => Physics.DipoleModelExamples.matrixModel,
  GUT.DipoleModelExamples.matrixModel.eq_1 => Physics.DipoleModelExamples.matrixModel.eq_1,
  GUT.DipoleModelExamples.matrix_nonzero_iff => Physics.DipoleModelExamples.matrix_nonzero_iff,
  GUT.DipoleModelExamples.matrix_selected => Physics.DipoleModelExamples.matrix_selected,
  GUT.DipoleModelExamples.residualModel => Physics.DipoleModelExamples.residualModel,
  GUT.DipoleModelExamples.residualModel.eq_1 => Physics.DipoleModelExamples.residualModel.eq_1,
  GUT.DipoleModelExamples.restricted_zero_unreachable => Physics.DipoleModelExamples.restricted_zero_unreachable
]

assert_compatible GUT.DipoleControls.generation.eq_1 => Physics.DipoleControls.generation.eq_1
assert_compatible GUT.DipoleMatrixInterface.register.congr_simp => Physics.DipoleMatrixInterface.register.congr_simp
assert_compatible GUT.DipoleModelExamples.cancelling => Physics.DipoleModelExamples.cancelling
assert_compatible GUT.DipoleModelExamples.cancelling.eq_1 => Physics.DipoleModelExamples.cancelling.eq_1
assert_compatible GUT.DipoleModelExamples.cancellingCertificate => Physics.DipoleModelExamples.cancellingCertificate
assert_compatible GUT.DipoleModelExamples.cancellingCertificate.eq_1 => Physics.DipoleModelExamples.cancellingCertificate.eq_1
assert_compatible GUT.DipoleModelExamples.cancellingPaths => Physics.DipoleModelExamples.cancellingPaths
assert_compatible GUT.DipoleModelExamples.cancellingPaths.eq_1 => Physics.DipoleModelExamples.cancellingPaths.eq_1
assert_compatible GUT.DipoleModelExamples.cancelling_no_nonzero => Physics.DipoleModelExamples.cancelling_no_nonzero
assert_compatible GUT.DipoleModelExamples.correlated => Physics.DipoleModelExamples.correlated
assert_compatible GUT.DipoleModelExamples.correlated_nonzero_iff => Physics.DipoleModelExamples.correlated_nonzero_iff
assert_compatible GUT.DipoleModelExamples.correlated_selected => Physics.DipoleModelExamples.correlated_selected
assert_compatible GUT.DipoleModelExamples.cubic => Physics.DipoleModelExamples.cubic
assert_compatible GUT.DipoleModelExamples.cubic.eq_1 => Physics.DipoleModelExamples.cubic.eq_1
assert_compatible GUT.DipoleModelExamples.cubicCertificate => Physics.DipoleModelExamples.cubicCertificate
assert_compatible GUT.DipoleModelExamples.cubicCertificate.eq_1 => Physics.DipoleModelExamples.cubicCertificate.eq_1
assert_compatible GUT.DipoleModelExamples.cubicPaths => Physics.DipoleModelExamples.cubicPaths
assert_compatible GUT.DipoleModelExamples.cubicPaths.eq_1 => Physics.DipoleModelExamples.cubicPaths.eq_1
assert_compatible GUT.DipoleModelExamples.cubicWeights => Physics.DipoleModelExamples.cubicWeights
assert_compatible GUT.DipoleModelExamples.cubicWeights.eq_1 => Physics.DipoleModelExamples.cubicWeights.eq_1
assert_compatible GUT.DipoleModelExamples.cubic_realized => Physics.DipoleModelExamples.cubic_realized
assert_compatible GUT.DipoleModelExamples.externalModel => Physics.DipoleModelExamples.externalModel
assert_compatible GUT.DipoleModelExamples.external_nonzero_iff => Physics.DipoleModelExamples.external_nonzero_iff
assert_compatible GUT.DipoleModelExamples.matrices => Physics.DipoleModelExamples.matrices
assert_compatible GUT.DipoleModelExamples.matrices.eq_1 => Physics.DipoleModelExamples.matrices.eq_1
assert_compatible GUT.DipoleModelExamples.matrixModel => Physics.DipoleModelExamples.matrixModel
assert_compatible GUT.DipoleModelExamples.matrixModel.eq_1 => Physics.DipoleModelExamples.matrixModel.eq_1
assert_compatible GUT.DipoleModelExamples.matrix_nonzero_iff => Physics.DipoleModelExamples.matrix_nonzero_iff
assert_compatible GUT.DipoleModelExamples.matrix_selected => Physics.DipoleModelExamples.matrix_selected
assert_compatible GUT.DipoleModelExamples.residualModel => Physics.DipoleModelExamples.residualModel
assert_compatible GUT.DipoleModelExamples.residualModel.eq_1 => Physics.DipoleModelExamples.residualModel.eq_1
assert_compatible GUT.DipoleModelExamples.restricted_zero_unreachable => Physics.DipoleModelExamples.restricted_zero_unreachable
