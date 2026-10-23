import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkConvention
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.LiSixQuarkFiniteData
import Physics.StandardModel.Operators.LiSixQuarkSourceTransport
import Physics.StandardModel.Operators.LiSixQuarkReducedSeeds
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkConvention instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkConvention.basisEntry.eq_1 => Physics.LiSixQuarkConvention.basisEntry.eq_1,
  GUT.LiSixQuarkConvention.candidate => Physics.LiSixQuarkConvention.candidate,
  GUT.LiSixQuarkConvention.candidate_basis => Physics.LiSixQuarkConvention.candidate_basis,
  GUT.LiSixQuarkConvention.candidate_coordinates => Physics.LiSixQuarkConvention.candidate_coordinates,
  GUT.LiSixQuarkConvention.candidate_invariant => Physics.LiSixQuarkConvention.candidate_invariant,
  GUT.LiSixQuarkConvention.colorEpsilon.eq_1 => Physics.LiSixQuarkConvention.colorEpsilon.eq_1,
  GUT.LiSixQuarkConvention.colorEpsilon_cast => Physics.LiSixQuarkConvention.colorEpsilon_cast,
  GUT.LiSixQuarkConvention.extra_agrees => Physics.LiSixQuarkConvention.extra_agrees,
  GUT.LiSixQuarkConvention.paperToRepo => Physics.LiSixQuarkConvention.paperToRepo,
  GUT.LiSixQuarkConvention.permutation => Physics.LiSixQuarkConvention.permutation,
  GUT.LiSixQuarkConvention.rationalValue.eq_1 => Physics.LiSixQuarkConvention.rationalValue.eq_1,
  GUT.LiSixQuarkConvention.seed => Physics.LiSixQuarkConvention.seed,
  GUT.LiSixQuarkConvention.seedColorPerm => Physics.LiSixQuarkConvention.seedColorPerm,
  GUT.LiSixQuarkConvention.seedCoordinates_semantic => Physics.LiSixQuarkConvention.seedCoordinates_semantic,
  GUT.LiSixQuarkConvention.spinEpsilon.eq_1 => Physics.LiSixQuarkConvention.spinEpsilon.eq_1,
  GUT.LiSixQuarkConvention.spinEpsilon_cast => Physics.LiSixQuarkConvention.spinEpsilon_cast,
  GUT.LiSixQuarkConvention.spinPerm => Physics.LiSixQuarkConvention.spinPerm,
  GUT.LiSixQuarkLiteralSource.permutation.eq_1 => Physics.LiSixQuarkLiteralSource.permutation.eq_1
]

assert_compatible GUT.LiSixQuarkConvention.basisEntry.eq_1 => Physics.LiSixQuarkConvention.basisEntry.eq_1
assert_compatible GUT.LiSixQuarkConvention.candidate => Physics.LiSixQuarkConvention.candidate
assert_compatible GUT.LiSixQuarkConvention.candidate_basis => Physics.LiSixQuarkConvention.candidate_basis
assert_compatible GUT.LiSixQuarkConvention.candidate_coordinates => Physics.LiSixQuarkConvention.candidate_coordinates
assert_compatible GUT.LiSixQuarkConvention.candidate_invariant => Physics.LiSixQuarkConvention.candidate_invariant
assert_compatible GUT.LiSixQuarkConvention.colorEpsilon.eq_1 => Physics.LiSixQuarkConvention.colorEpsilon.eq_1
assert_compatible GUT.LiSixQuarkConvention.colorEpsilon_cast => Physics.LiSixQuarkConvention.colorEpsilon_cast
assert_compatible GUT.LiSixQuarkConvention.extra_agrees => Physics.LiSixQuarkConvention.extra_agrees
assert_compatible GUT.LiSixQuarkConvention.paperToRepo => Physics.LiSixQuarkConvention.paperToRepo
assert_compatible GUT.LiSixQuarkConvention.permutation => Physics.LiSixQuarkConvention.permutation
assert_compatible GUT.LiSixQuarkConvention.rationalValue.eq_1 => Physics.LiSixQuarkConvention.rationalValue.eq_1
assert_compatible GUT.LiSixQuarkConvention.seed => Physics.LiSixQuarkConvention.seed
assert_compatible GUT.LiSixQuarkConvention.seedColorPerm => Physics.LiSixQuarkConvention.seedColorPerm
assert_compatible GUT.LiSixQuarkConvention.seedCoordinates_semantic => Physics.LiSixQuarkConvention.seedCoordinates_semantic
assert_compatible GUT.LiSixQuarkConvention.spinEpsilon.eq_1 => Physics.LiSixQuarkConvention.spinEpsilon.eq_1
assert_compatible GUT.LiSixQuarkConvention.spinEpsilon_cast => Physics.LiSixQuarkConvention.spinEpsilon_cast
assert_compatible GUT.LiSixQuarkConvention.spinPerm => Physics.LiSixQuarkConvention.spinPerm
assert_compatible GUT.LiSixQuarkLiteralSource.permutation.eq_1 => Physics.LiSixQuarkLiteralSource.permutation.eq_1
