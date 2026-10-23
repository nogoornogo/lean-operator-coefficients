import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkRawSource
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.SixQuarkFlavorCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkRawSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkRawSource.colorCoordinates => Physics.LiSixQuarkRawSource.colorCoordinates,
  GUT.LiSixQuarkRawSource.colorCoordinates.eq_1 => Physics.LiSixQuarkRawSource.colorCoordinates.eq_1,
  GUT.LiSixQuarkRawSource.colorKind => Physics.LiSixQuarkRawSource.colorKind,
  GUT.LiSixQuarkRawSource.colorPermutation => Physics.LiSixQuarkRawSource.colorPermutation,
  GUT.LiSixQuarkRawSource.colorPermutation.eq_1 => Physics.LiSixQuarkRawSource.colorPermutation.eq_1,
  GUT.LiSixQuarkRawSource.rawCoefficient => Physics.LiSixQuarkRawSource.rawCoefficient,
  GUT.LiSixQuarkRawSource.rawCoefficient.eq_1 => Physics.LiSixQuarkRawSource.rawCoefficient.eq_1,
  GUT.LiSixQuarkRawSource.rawCoefficient_reconstruct => Physics.LiSixQuarkRawSource.rawCoefficient_reconstruct,
  GUT.LiSixQuarkRawSource.rawColor => Physics.LiSixQuarkRawSource.rawColor,
  GUT.LiSixQuarkRawSource.rawColor.eq_1 => Physics.LiSixQuarkRawSource.rawColor.eq_1,
  GUT.LiSixQuarkRawSource.rawColor_reconstruct => Physics.LiSixQuarkRawSource.rawColor_reconstruct,
  GUT.LiSixQuarkRawSource.rawCoordinates => Physics.LiSixQuarkRawSource.rawCoordinates,
  GUT.LiSixQuarkRawSource.rawSpin => Physics.LiSixQuarkRawSource.rawSpin,
  GUT.LiSixQuarkRawSource.rawSpin.eq_1 => Physics.LiSixQuarkRawSource.rawSpin.eq_1,
  GUT.LiSixQuarkRawSource.rawSpin_reconstruct => Physics.LiSixQuarkRawSource.rawSpin_reconstruct,
  GUT.LiSixQuarkRawSource.reconstruct_outer => Physics.LiSixQuarkRawSource.reconstruct_outer,
  GUT.LiSixQuarkRawSource.spinCoordinates => Physics.LiSixQuarkRawSource.spinCoordinates,
  GUT.LiSixQuarkRawSource.spinCoordinates.eq_1 => Physics.LiSixQuarkRawSource.spinCoordinates.eq_1,
  GUT.LiSixQuarkRawSource.spinPermutation => Physics.LiSixQuarkRawSource.spinPermutation,
  GUT.LiSixQuarkRawSource.spinPermutation.eq_1 => Physics.LiSixQuarkRawSource.spinPermutation.eq_1
]

assert_compatible GUT.LiSixQuarkRawSource.colorCoordinates => Physics.LiSixQuarkRawSource.colorCoordinates
assert_compatible GUT.LiSixQuarkRawSource.colorCoordinates.eq_1 => Physics.LiSixQuarkRawSource.colorCoordinates.eq_1
assert_compatible GUT.LiSixQuarkRawSource.colorKind => Physics.LiSixQuarkRawSource.colorKind
assert_compatible GUT.LiSixQuarkRawSource.colorPermutation => Physics.LiSixQuarkRawSource.colorPermutation
assert_compatible GUT.LiSixQuarkRawSource.colorPermutation.eq_1 => Physics.LiSixQuarkRawSource.colorPermutation.eq_1
assert_compatible GUT.LiSixQuarkRawSource.rawCoefficient => Physics.LiSixQuarkRawSource.rawCoefficient
assert_compatible GUT.LiSixQuarkRawSource.rawCoefficient.eq_1 => Physics.LiSixQuarkRawSource.rawCoefficient.eq_1
assert_compatible GUT.LiSixQuarkRawSource.rawCoefficient_reconstruct => Physics.LiSixQuarkRawSource.rawCoefficient_reconstruct
assert_compatible GUT.LiSixQuarkRawSource.rawColor => Physics.LiSixQuarkRawSource.rawColor
assert_compatible GUT.LiSixQuarkRawSource.rawColor.eq_1 => Physics.LiSixQuarkRawSource.rawColor.eq_1
assert_compatible GUT.LiSixQuarkRawSource.rawColor_reconstruct => Physics.LiSixQuarkRawSource.rawColor_reconstruct
assert_compatible GUT.LiSixQuarkRawSource.rawCoordinates => Physics.LiSixQuarkRawSource.rawCoordinates
assert_compatible GUT.LiSixQuarkRawSource.rawSpin => Physics.LiSixQuarkRawSource.rawSpin
assert_compatible GUT.LiSixQuarkRawSource.rawSpin.eq_1 => Physics.LiSixQuarkRawSource.rawSpin.eq_1
assert_compatible GUT.LiSixQuarkRawSource.rawSpin_reconstruct => Physics.LiSixQuarkRawSource.rawSpin_reconstruct
assert_compatible GUT.LiSixQuarkRawSource.reconstruct_outer => Physics.LiSixQuarkRawSource.reconstruct_outer
assert_compatible GUT.LiSixQuarkRawSource.spinCoordinates => Physics.LiSixQuarkRawSource.spinCoordinates
assert_compatible GUT.LiSixQuarkRawSource.spinCoordinates.eq_1 => Physics.LiSixQuarkRawSource.spinCoordinates.eq_1
assert_compatible GUT.LiSixQuarkRawSource.spinPermutation => Physics.LiSixQuarkRawSource.spinPermutation
assert_compatible GUT.LiSixQuarkRawSource.spinPermutation.eq_1 => Physics.LiSixQuarkRawSource.spinPermutation.eq_1
