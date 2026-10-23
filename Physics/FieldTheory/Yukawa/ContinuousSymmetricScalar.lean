import Physics.FieldTheory.Yukawa.Mass.ContinuousSymmetricScalar
import Physics.FieldTheory.Yukawa.SymmetricScalarYukawa
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.ContinuousSymmetricScalar instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ContinuousSymmetricScalar.ScalarCopy => Physics.ContinuousSymmetricScalar.ScalarCopy,
  GUT.ContinuousSymmetricScalar.matrixCoordinates => Physics.ContinuousSymmetricScalar.matrixCoordinates,
  GUT.ContinuousSymmetricScalar.matrixCoordinates_injective => Physics.ContinuousSymmetricScalar.matrixCoordinates_injective,
  GUT.ContinuousSymmetricScalar.scalarBasis => Physics.ContinuousSymmetricScalar.scalarBasis,
  GUT.ContinuousSymmetricScalar.scalarFree => Physics.ContinuousSymmetricScalar.scalarFree,
  GUT.ContinuousSymmetricScalar.seedEquiv => Physics.ContinuousSymmetricScalar.seedEquiv,
  GUT.ContinuousSymmetricScalar.seedRho => Physics.ContinuousSymmetricScalar.seedRho,
  GUT.ContinuousSymmetricScalar.seed_jointlyContinuous => Physics.ContinuousSymmetricScalar.seed_jointlyContinuous
]

assert_compatible GUT.ContinuousSymmetricScalar.ScalarCopy => Physics.ContinuousSymmetricScalar.ScalarCopy
assert_compatible GUT.ContinuousSymmetricScalar.matrixCoordinates => Physics.ContinuousSymmetricScalar.matrixCoordinates
assert_compatible GUT.ContinuousSymmetricScalar.matrixCoordinates_injective => Physics.ContinuousSymmetricScalar.matrixCoordinates_injective
assert_compatible GUT.ContinuousSymmetricScalar.scalarBasis => Physics.ContinuousSymmetricScalar.scalarBasis
assert_compatible GUT.ContinuousSymmetricScalar.scalarFree => Physics.ContinuousSymmetricScalar.scalarFree
assert_compatible GUT.ContinuousSymmetricScalar.seedEquiv => Physics.ContinuousSymmetricScalar.seedEquiv
assert_compatible GUT.ContinuousSymmetricScalar.seedRho => Physics.ContinuousSymmetricScalar.seedRho
assert_compatible GUT.ContinuousSymmetricScalar.seed_jointlyContinuous => Physics.ContinuousSymmetricScalar.seed_jointlyContinuous
