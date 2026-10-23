import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLiteralSource
import Physics.StandardModel.Operators.LiSixQuarkExtension
import Physics.StandardModel.Operators.LiSixQuarkYoungData
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkLiteralSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkLiteralSource.candidate => Physics.LiSixQuarkLiteralSource.candidate,
  GUT.LiSixQuarkLiteralSource.candidate_invariant => Physics.LiSixQuarkLiteralSource.candidate_invariant,
  GUT.LiSixQuarkLiteralSource.paperToRepo => Physics.LiSixQuarkLiteralSource.paperToRepo,
  GUT.LiSixQuarkLiteralSource.permutation => Physics.LiSixQuarkLiteralSource.permutation,
  GUT.LiSixQuarkLiteralSource.seed => Physics.LiSixQuarkLiteralSource.seed,
  GUT.LiSixQuarkLiteralSource.seedColorPerm => Physics.LiSixQuarkLiteralSource.seedColorPerm,
  GUT.LiSixQuarkLiteralSource.spinPerm => Physics.LiSixQuarkLiteralSource.spinPerm
]

assert_compatible GUT.LiSixQuarkLiteralSource.candidate => Physics.LiSixQuarkLiteralSource.candidate
assert_compatible GUT.LiSixQuarkLiteralSource.candidate_invariant => Physics.LiSixQuarkLiteralSource.candidate_invariant
assert_compatible GUT.LiSixQuarkLiteralSource.paperToRepo => Physics.LiSixQuarkLiteralSource.paperToRepo
assert_compatible GUT.LiSixQuarkLiteralSource.permutation => Physics.LiSixQuarkLiteralSource.permutation
assert_compatible GUT.LiSixQuarkLiteralSource.seed => Physics.LiSixQuarkLiteralSource.seed
assert_compatible GUT.LiSixQuarkLiteralSource.seedColorPerm => Physics.LiSixQuarkLiteralSource.seedColorPerm
assert_compatible GUT.LiSixQuarkLiteralSource.spinPerm => Physics.LiSixQuarkLiteralSource.spinPerm
