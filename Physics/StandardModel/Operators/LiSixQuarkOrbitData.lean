import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitData
import Physics.StandardModel.Operators.LiSixQuarkFiniteData
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitData instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkCertificate.columnR => Physics.LiSixQuarkCertificate.columnR,
  GUT.LiSixQuarkCertificate.columnR.eq_1 => Physics.LiSixQuarkCertificate.columnR.eq_1,
  GUT.LiSixQuarkCertificate.orbitR_agrees => Physics.LiSixQuarkCertificate.orbitR_agrees,
  GUT.LiSixQuarkCertificate.orbit_column => Physics.LiSixQuarkCertificate.orbit_column
]

assert_compatible GUT.LiSixQuarkCertificate.columnR => Physics.LiSixQuarkCertificate.columnR
assert_compatible GUT.LiSixQuarkCertificate.columnR.eq_1 => Physics.LiSixQuarkCertificate.columnR.eq_1
assert_compatible GUT.LiSixQuarkCertificate.orbitR_agrees => Physics.LiSixQuarkCertificate.orbitR_agrees
assert_compatible GUT.LiSixQuarkCertificate.orbit_column => Physics.LiSixQuarkCertificate.orbit_column
