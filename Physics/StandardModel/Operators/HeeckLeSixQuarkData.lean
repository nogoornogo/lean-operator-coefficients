import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkData
import Physics.StandardModel.Operators.HeeckLeSixQuarkMatrix
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkData instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkCertificate.basisRational => Physics.HeeckLeSixQuarkCertificate.basisRational,
  GUT.HeeckLeSixQuarkCertificate.columnR => Physics.HeeckLeSixQuarkCertificate.columnR,
  GUT.HeeckLeSixQuarkCertificate.inverseRational => Physics.HeeckLeSixQuarkCertificate.inverseRational,
  GUT.HeeckLeSixQuarkCertificate.orbitR => Physics.HeeckLeSixQuarkCertificate.orbitR,
  GUT.HeeckLeSixQuarkCertificate.orbitR_agrees => Physics.HeeckLeSixQuarkCertificate.orbitR_agrees,
  GUT.HeeckLeSixQuarkCertificate.rationalSeedCoordinates => Physics.HeeckLeSixQuarkCertificate.rationalSeedCoordinates,
  GUT.HeeckLeSixQuarkCertificate.rational_left_inverse => Physics.HeeckLeSixQuarkCertificate.rational_left_inverse,
  GUT.HeeckLeSixQuarkCertificate.rational_right_inverse => Physics.HeeckLeSixQuarkCertificate.rational_right_inverse,
  GUT.HeeckLeSixQuarkCertificate.selectedSeed => Physics.HeeckLeSixQuarkCertificate.selectedSeed,
  GUT.HeeckLeSixQuarkCertificate.selectedWord => Physics.HeeckLeSixQuarkCertificate.selectedWord
]

assert_compatible GUT.HeeckLeSixQuarkCertificate.basisRational => Physics.HeeckLeSixQuarkCertificate.basisRational
assert_compatible GUT.HeeckLeSixQuarkCertificate.columnR => Physics.HeeckLeSixQuarkCertificate.columnR
assert_compatible GUT.HeeckLeSixQuarkCertificate.inverseRational => Physics.HeeckLeSixQuarkCertificate.inverseRational
assert_compatible GUT.HeeckLeSixQuarkCertificate.orbitR => Physics.HeeckLeSixQuarkCertificate.orbitR
assert_compatible GUT.HeeckLeSixQuarkCertificate.orbitR_agrees => Physics.HeeckLeSixQuarkCertificate.orbitR_agrees
assert_compatible GUT.HeeckLeSixQuarkCertificate.rationalSeedCoordinates => Physics.HeeckLeSixQuarkCertificate.rationalSeedCoordinates
assert_compatible GUT.HeeckLeSixQuarkCertificate.rational_left_inverse => Physics.HeeckLeSixQuarkCertificate.rational_left_inverse
assert_compatible GUT.HeeckLeSixQuarkCertificate.rational_right_inverse => Physics.HeeckLeSixQuarkCertificate.rational_right_inverse
assert_compatible GUT.HeeckLeSixQuarkCertificate.selectedSeed => Physics.HeeckLeSixQuarkCertificate.selectedSeed
assert_compatible GUT.HeeckLeSixQuarkCertificate.selectedWord => Physics.HeeckLeSixQuarkCertificate.selectedWord
