import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate
import Math.Algebra.ScalarZeroDerivative
import Physics.FieldTheory.Jets.ScalarConstantCoefficients
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarZeroDerivativeCertificate.Image => Physics.ScalarZeroDerivativeCertificate.Image,
  GUT.ScalarZeroDerivativeCertificate.P => Physics.ScalarZeroDerivativeCertificate.P,
  GUT.ScalarZeroDerivativeCertificate.V => Physics.ScalarZeroDerivativeCertificate.V,
  GUT.ScalarZeroDerivativeCertificate.coordinate => Physics.ScalarZeroDerivativeCertificate.coordinate,
  GUT.ScalarZeroDerivativeCertificate.coordinate_generator => Physics.ScalarZeroDerivativeCertificate.coordinate_generator,
  GUT.ScalarZeroDerivativeCertificate.dimension => Physics.ScalarZeroDerivativeCertificate.dimension,
  GUT.ScalarZeroDerivativeCertificate.equivalence => Physics.ScalarZeroDerivativeCertificate.equivalence,
  GUT.ScalarZeroDerivativeCertificate.four_scalar_dimension => Physics.ScalarZeroDerivativeCertificate.four_scalar_dimension,
  GUT.ScalarZeroDerivativeCertificate.generator => Physics.ScalarZeroDerivativeCertificate.generator,
  GUT.ScalarZeroDerivativeCertificate.reconstruction => Physics.ScalarZeroDerivativeCertificate.reconstruction
]

assert_compatible GUT.ScalarZeroDerivativeCertificate.Image => Physics.ScalarZeroDerivativeCertificate.Image
assert_compatible GUT.ScalarZeroDerivativeCertificate.P => Physics.ScalarZeroDerivativeCertificate.P
assert_compatible GUT.ScalarZeroDerivativeCertificate.V => Physics.ScalarZeroDerivativeCertificate.V
assert_compatible GUT.ScalarZeroDerivativeCertificate.coordinate => Physics.ScalarZeroDerivativeCertificate.coordinate
assert_compatible GUT.ScalarZeroDerivativeCertificate.coordinate_generator => Physics.ScalarZeroDerivativeCertificate.coordinate_generator
assert_compatible GUT.ScalarZeroDerivativeCertificate.dimension => Physics.ScalarZeroDerivativeCertificate.dimension
assert_compatible GUT.ScalarZeroDerivativeCertificate.equivalence => Physics.ScalarZeroDerivativeCertificate.equivalence
assert_compatible GUT.ScalarZeroDerivativeCertificate.four_scalar_dimension => Physics.ScalarZeroDerivativeCertificate.four_scalar_dimension
assert_compatible GUT.ScalarZeroDerivativeCertificate.generator => Physics.ScalarZeroDerivativeCertificate.generator
assert_compatible GUT.ScalarZeroDerivativeCertificate.reconstruction => Physics.ScalarZeroDerivativeCertificate.reconstruction
