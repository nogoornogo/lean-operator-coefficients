import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkConvention
import Physics.StandardModel.Operators.HeeckLeSixQuarkData
import Physics.StandardModel.Operators.LiSixQuarkLocalBasis
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkCertificate.color_identity => Physics.HeeckLeSixQuarkCertificate.color_identity,
  GUT.HeeckLeSixQuarkCertificate.literal => Physics.HeeckLeSixQuarkCertificate.literal,
  GUT.HeeckLeSixQuarkCertificate.orbitArray => Physics.HeeckLeSixQuarkCertificate.orbitArray,
  GUT.HeeckLeSixQuarkCertificate.orbitCoefficient => Physics.HeeckLeSixQuarkCertificate.orbitCoefficient,
  GUT.HeeckLeSixQuarkCertificate.orbitCoefficient_eq => Physics.HeeckLeSixQuarkCertificate.orbitCoefficient_eq,
  GUT.HeeckLeSixQuarkCertificate.paperColor => Physics.HeeckLeSixQuarkCertificate.paperColor,
  GUT.HeeckLeSixQuarkCertificate.paperColor.eq_1 => Physics.HeeckLeSixQuarkCertificate.paperColor.eq_1,
  GUT.HeeckLeSixQuarkCertificate.seed => Physics.HeeckLeSixQuarkCertificate.seed,
  GUT.HeeckLeSixQuarkCertificate.seed.eq_1 => Physics.HeeckLeSixQuarkCertificate.seed.eq_1,
  GUT.HeeckLeSixQuarkCertificate.seedCoordinates => Physics.HeeckLeSixQuarkCertificate.seedCoordinates,
  GUT.HeeckLeSixQuarkCertificate.seedCoordinates.eq_1 => Physics.HeeckLeSixQuarkCertificate.seedCoordinates.eq_1,
  GUT.HeeckLeSixQuarkCertificate.seed_spin_zero => Physics.HeeckLeSixQuarkCertificate.seed_spin_zero,
  GUT.HeeckLeSixQuarkRecipe.seed.eq_1 => Physics.HeeckLeSixQuarkRecipe.seed.eq_1
]

assert_compatible GUT.HeeckLeSixQuarkCertificate.color_identity => Physics.HeeckLeSixQuarkCertificate.color_identity
assert_compatible GUT.HeeckLeSixQuarkCertificate.literal => Physics.HeeckLeSixQuarkCertificate.literal
assert_compatible GUT.HeeckLeSixQuarkCertificate.orbitArray => Physics.HeeckLeSixQuarkCertificate.orbitArray
assert_compatible GUT.HeeckLeSixQuarkCertificate.orbitCoefficient => Physics.HeeckLeSixQuarkCertificate.orbitCoefficient
assert_compatible GUT.HeeckLeSixQuarkCertificate.orbitCoefficient_eq => Physics.HeeckLeSixQuarkCertificate.orbitCoefficient_eq
assert_compatible GUT.HeeckLeSixQuarkCertificate.paperColor => Physics.HeeckLeSixQuarkCertificate.paperColor
assert_compatible GUT.HeeckLeSixQuarkCertificate.paperColor.eq_1 => Physics.HeeckLeSixQuarkCertificate.paperColor.eq_1
assert_compatible GUT.HeeckLeSixQuarkCertificate.seed => Physics.HeeckLeSixQuarkCertificate.seed
assert_compatible GUT.HeeckLeSixQuarkCertificate.seed.eq_1 => Physics.HeeckLeSixQuarkCertificate.seed.eq_1
assert_compatible GUT.HeeckLeSixQuarkCertificate.seedCoordinates => Physics.HeeckLeSixQuarkCertificate.seedCoordinates
assert_compatible GUT.HeeckLeSixQuarkCertificate.seedCoordinates.eq_1 => Physics.HeeckLeSixQuarkCertificate.seedCoordinates.eq_1
assert_compatible GUT.HeeckLeSixQuarkCertificate.seed_spin_zero => Physics.HeeckLeSixQuarkCertificate.seed_spin_zero
assert_compatible GUT.HeeckLeSixQuarkRecipe.seed.eq_1 => Physics.HeeckLeSixQuarkRecipe.seed.eq_1
