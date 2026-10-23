import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitRecipe
import Physics.StandardModel.Operators.LiSixQuarkSeedRecipe
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkOrbitRecipe instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkCertificate.basisRational => Physics.LiSixQuarkCertificate.basisRational,
  GUT.LiSixQuarkCertificate.colorMatrixR => Physics.LiSixQuarkCertificate.colorMatrixR,
  GUT.LiSixQuarkCertificate.orbitR => Physics.LiSixQuarkCertificate.orbitR,
  GUT.LiSixQuarkCertificate.selectedSeed => Physics.LiSixQuarkCertificate.selectedSeed,
  GUT.LiSixQuarkCertificate.selectedWord => Physics.LiSixQuarkCertificate.selectedWord,
  GUT.LiSixQuarkCertificate.spinMatrixR => Physics.LiSixQuarkCertificate.spinMatrixR,
  GUT.LiSixQuarkCertificate.transformR => Physics.LiSixQuarkCertificate.transformR
]

assert_compatible GUT.LiSixQuarkCertificate.basisRational => Physics.LiSixQuarkCertificate.basisRational
assert_compatible GUT.LiSixQuarkCertificate.colorMatrixR => Physics.LiSixQuarkCertificate.colorMatrixR
assert_compatible GUT.LiSixQuarkCertificate.orbitR => Physics.LiSixQuarkCertificate.orbitR
assert_compatible GUT.LiSixQuarkCertificate.selectedSeed => Physics.LiSixQuarkCertificate.selectedSeed
assert_compatible GUT.LiSixQuarkCertificate.selectedWord => Physics.LiSixQuarkCertificate.selectedWord
assert_compatible GUT.LiSixQuarkCertificate.spinMatrixR => Physics.LiSixQuarkCertificate.spinMatrixR
assert_compatible GUT.LiSixQuarkCertificate.transformR => Physics.LiSixQuarkCertificate.transformR
