import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarRealityChecks
import Math.Algebra.PolynomialJetConjugation
import Math.Algebra.SemilinearDifferentialRelations
import Math.LinearAlgebra.HermitianCoefficientChecks
import Physics.FieldTheory.Jets.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.WeylJetAdjoint
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarRealityChecks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PolynomialScalarEOM.equations.eq_1 => Physics.PolynomialScalarEOM.equations.eq_1,
  GUT.ScalarRealityChecks.T => Physics.ScalarRealityChecks.T,
  GUT.ScalarRealityChecks.adjoint => Physics.ScalarRealityChecks.adjoint,
  GUT.ScalarRealityChecks.adjoint_action => Physics.ScalarRealityChecks.adjoint_action,
  GUT.ScalarRealityChecks.adjoint_involutive => Physics.ScalarRealityChecks.adjoint_involutive,
  GUT.ScalarRealityChecks.adjoint_projection => Physics.ScalarRealityChecks.adjoint_projection,
  GUT.ScalarRealityChecks.conjugation_action => Physics.ScalarRealityChecks.conjugation_action,
  GUT.ScalarRealityChecks.free_power_real_iff => Physics.ScalarRealityChecks.free_power_real_iff,
  GUT.ScalarRealityChecks.image_fixed_iff => Physics.ScalarRealityChecks.image_fixed_iff,
  GUT.ScalarRealityChecks.paired_left_conjugate_zero => Physics.ScalarRealityChecks.paired_left_conjugate_zero,
  GUT.ScalarRealityChecks.paired_weyl_action => Physics.ScalarRealityChecks.paired_weyl_action,
  GUT.ScalarRealityChecks.paired_weyl_derivative => Physics.ScalarRealityChecks.paired_weyl_derivative,
  GUT.ScalarRealityChecks.paired_weyl_involutive => Physics.ScalarRealityChecks.paired_weyl_involutive,
  GUT.ScalarRealityChecks.power_fixed => Physics.ScalarRealityChecks.power_fixed,
  GUT.ScalarRealityChecks.realImage => Physics.ScalarRealityChecks.realImage,
  GUT.ScalarRealityChecks.realImageEquiv => Physics.ScalarRealityChecks.realImageEquiv,
  GUT.ScalarRealityChecks.realImage_iff => Physics.ScalarRealityChecks.realImage_iff,
  GUT.ScalarRealityChecks.real_image_dimension => Physics.ScalarRealityChecks.real_image_dimension,
  GUT.ScalarRealityChecks.seed_conjugate => Physics.ScalarRealityChecks.seed_conjugate,
  GUT.ScalarRealityChecks.stable => Physics.ScalarRealityChecks.stable,
  GUT.ScalarZeroDerivativeCertificate.generator.eq_1 => Physics.ScalarZeroDerivativeCertificate.generator.eq_1
]

assert_compatible GUT.PolynomialScalarEOM.equations.eq_1 => Physics.PolynomialScalarEOM.equations.eq_1
assert_compatible GUT.ScalarRealityChecks.T => Physics.ScalarRealityChecks.T
assert_compatible GUT.ScalarRealityChecks.adjoint => Physics.ScalarRealityChecks.adjoint
assert_compatible GUT.ScalarRealityChecks.adjoint_action => Physics.ScalarRealityChecks.adjoint_action
assert_compatible GUT.ScalarRealityChecks.adjoint_involutive => Physics.ScalarRealityChecks.adjoint_involutive
assert_compatible GUT.ScalarRealityChecks.adjoint_projection => Physics.ScalarRealityChecks.adjoint_projection
assert_compatible GUT.ScalarRealityChecks.conjugation_action => Physics.ScalarRealityChecks.conjugation_action
assert_compatible GUT.ScalarRealityChecks.free_power_real_iff => Physics.ScalarRealityChecks.free_power_real_iff
assert_compatible GUT.ScalarRealityChecks.image_fixed_iff => Physics.ScalarRealityChecks.image_fixed_iff
assert_compatible GUT.ScalarRealityChecks.paired_left_conjugate_zero => Physics.ScalarRealityChecks.paired_left_conjugate_zero
assert_compatible GUT.ScalarRealityChecks.paired_weyl_action => Physics.ScalarRealityChecks.paired_weyl_action
assert_compatible GUT.ScalarRealityChecks.paired_weyl_derivative => Physics.ScalarRealityChecks.paired_weyl_derivative
assert_compatible GUT.ScalarRealityChecks.paired_weyl_involutive => Physics.ScalarRealityChecks.paired_weyl_involutive
assert_compatible GUT.ScalarRealityChecks.power_fixed => Physics.ScalarRealityChecks.power_fixed
assert_compatible GUT.ScalarRealityChecks.realImage => Physics.ScalarRealityChecks.realImage
assert_compatible GUT.ScalarRealityChecks.realImageEquiv => Physics.ScalarRealityChecks.realImageEquiv
assert_compatible GUT.ScalarRealityChecks.realImage_iff => Physics.ScalarRealityChecks.realImage_iff
assert_compatible GUT.ScalarRealityChecks.real_image_dimension => Physics.ScalarRealityChecks.real_image_dimension
assert_compatible GUT.ScalarRealityChecks.seed_conjugate => Physics.ScalarRealityChecks.seed_conjugate
assert_compatible GUT.ScalarRealityChecks.stable => Physics.ScalarRealityChecks.stable
assert_compatible GUT.ScalarZeroDerivativeCertificate.generator.eq_1 => Physics.ScalarZeroDerivativeCertificate.generator.eq_1
