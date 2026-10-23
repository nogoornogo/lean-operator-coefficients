import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSourceTransport
import Physics.StandardModel.Operators.LiSixQuarkLiteralSource
import Physics.StandardModel.Operators.LiSixQuarkSemanticSeeds
import Physics.StandardModel.Operators.LiSixQuarkYoungExpansion
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSourceTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkLiteralSource.candidate.eq_1 => Physics.LiSixQuarkLiteralSource.candidate.eq_1,
  GUT.LiSixQuarkLiteralSource.paperToRepo.eq_1 => Physics.LiSixQuarkLiteralSource.paperToRepo.eq_1,
  GUT.LiSixQuarkLiteralSource.seed.eq_1 => Physics.LiSixQuarkLiteralSource.seed.eq_1,
  GUT.LiSixQuarkLiteralSource.seedColorPerm.eq_1 => Physics.LiSixQuarkLiteralSource.seedColorPerm.eq_1,
  GUT.LiSixQuarkLiteralSource.spinPerm.eq_1 => Physics.LiSixQuarkLiteralSource.spinPerm.eq_1,
  GUT.LiSixQuarkRawSource.colorKind.eq_1 => Physics.LiSixQuarkRawSource.colorKind.eq_1,
  GUT.LiSixQuarkRawSource.colorKind.eq_2 => Physics.LiSixQuarkRawSource.colorKind.eq_2,
  GUT.LiSixQuarkRawSource.colorKind.eq_3 => Physics.LiSixQuarkRawSource.colorKind.eq_3,
  GUT.LiSixQuarkRawSource.colorKind.eq_4 => Physics.LiSixQuarkRawSource.colorKind.eq_4,
  GUT.LiSixQuarkRawSource.colorKind.eq_5 => Physics.LiSixQuarkRawSource.colorKind.eq_5,
  GUT.LiSixQuarkRawSource.colorKind.eq_6 => Physics.LiSixQuarkRawSource.colorKind.eq_6,
  GUT.LiSixQuarkSourceTransport.candidate_coordinates => Physics.LiSixQuarkSourceTransport.candidate_coordinates,
  GUT.LiSixQuarkSourceTransport.candidate_eq_semantic => Physics.LiSixQuarkSourceTransport.candidate_eq_semantic,
  GUT.LiSixQuarkSourceTransport.evaluateLinear => Physics.LiSixQuarkSourceTransport.evaluateLinear,
  GUT.LiSixQuarkSourceTransport.evaluateLinear.eq_1 => Physics.LiSixQuarkSourceTransport.evaluateLinear.eq_1,
  GUT.LiSixQuarkSourceTransport.evaluate_action => Physics.LiSixQuarkSourceTransport.evaluate_action,
  GUT.LiSixQuarkSourceTransport.raw_source => Physics.LiSixQuarkSourceTransport.raw_source,
  GUT.LiSixQuarkYoungData.seedColorData.eq_1 => Physics.LiSixQuarkYoungData.seedColorData.eq_1
]

assert_compatible GUT.LiSixQuarkLiteralSource.candidate.eq_1 => Physics.LiSixQuarkLiteralSource.candidate.eq_1
assert_compatible GUT.LiSixQuarkLiteralSource.paperToRepo.eq_1 => Physics.LiSixQuarkLiteralSource.paperToRepo.eq_1
assert_compatible GUT.LiSixQuarkLiteralSource.seed.eq_1 => Physics.LiSixQuarkLiteralSource.seed.eq_1
assert_compatible GUT.LiSixQuarkLiteralSource.seedColorPerm.eq_1 => Physics.LiSixQuarkLiteralSource.seedColorPerm.eq_1
assert_compatible GUT.LiSixQuarkLiteralSource.spinPerm.eq_1 => Physics.LiSixQuarkLiteralSource.spinPerm.eq_1
assert_compatible GUT.LiSixQuarkRawSource.colorKind.eq_1 => Physics.LiSixQuarkRawSource.colorKind.eq_1
assert_compatible GUT.LiSixQuarkRawSource.colorKind.eq_2 => Physics.LiSixQuarkRawSource.colorKind.eq_2
assert_compatible GUT.LiSixQuarkRawSource.colorKind.eq_3 => Physics.LiSixQuarkRawSource.colorKind.eq_3
assert_compatible GUT.LiSixQuarkRawSource.colorKind.eq_4 => Physics.LiSixQuarkRawSource.colorKind.eq_4
assert_compatible GUT.LiSixQuarkRawSource.colorKind.eq_5 => Physics.LiSixQuarkRawSource.colorKind.eq_5
assert_compatible GUT.LiSixQuarkRawSource.colorKind.eq_6 => Physics.LiSixQuarkRawSource.colorKind.eq_6
assert_compatible GUT.LiSixQuarkSourceTransport.candidate_coordinates => Physics.LiSixQuarkSourceTransport.candidate_coordinates
assert_compatible GUT.LiSixQuarkSourceTransport.candidate_eq_semantic => Physics.LiSixQuarkSourceTransport.candidate_eq_semantic
assert_compatible GUT.LiSixQuarkSourceTransport.evaluateLinear => Physics.LiSixQuarkSourceTransport.evaluateLinear
assert_compatible GUT.LiSixQuarkSourceTransport.evaluateLinear.eq_1 => Physics.LiSixQuarkSourceTransport.evaluateLinear.eq_1
assert_compatible GUT.LiSixQuarkSourceTransport.evaluate_action => Physics.LiSixQuarkSourceTransport.evaluate_action
assert_compatible GUT.LiSixQuarkSourceTransport.raw_source => Physics.LiSixQuarkSourceTransport.raw_source
assert_compatible GUT.LiSixQuarkYoungData.seedColorData.eq_1 => Physics.LiSixQuarkYoungData.seedColorData.eq_1
