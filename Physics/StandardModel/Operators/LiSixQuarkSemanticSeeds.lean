import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSemanticSeeds
import Physics.StandardModel.Operators.LiSixQuarkLocalAction
import Physics.StandardModel.Operators.LiSixQuarkRawSource
import Physics.StandardModel.Operators.LiSixQuarkYoungOperators
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkSemanticSeeds instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiSixQuarkSemanticSeeds.coefficientAction => Physics.LiSixQuarkSemanticSeeds.coefficientAction,
  GUT.LiSixQuarkSemanticSeeds.coordinates_seedCoefficient => Physics.LiSixQuarkSemanticSeeds.coordinates_seedCoefficient,
  GUT.LiSixQuarkSemanticSeeds.reconstruct_action => Physics.LiSixQuarkSemanticSeeds.reconstruct_action,
  GUT.LiSixQuarkSemanticSeeds.seedCoefficient => Physics.LiSixQuarkSemanticSeeds.seedCoefficient,
  GUT.LiSixQuarkSemanticSeeds.seedCoefficient_reconstruct => Physics.LiSixQuarkSemanticSeeds.seedCoefficient_reconstruct,
  GUT.LiSixQuarkSemanticSeeds.seedCoordinates => Physics.LiSixQuarkSemanticSeeds.seedCoordinates
]

assert_compatible GUT.LiSixQuarkSemanticSeeds.coefficientAction => Physics.LiSixQuarkSemanticSeeds.coefficientAction
assert_compatible GUT.LiSixQuarkSemanticSeeds.coordinates_seedCoefficient => Physics.LiSixQuarkSemanticSeeds.coordinates_seedCoefficient
assert_compatible GUT.LiSixQuarkSemanticSeeds.reconstruct_action => Physics.LiSixQuarkSemanticSeeds.reconstruct_action
assert_compatible GUT.LiSixQuarkSemanticSeeds.seedCoefficient => Physics.LiSixQuarkSemanticSeeds.seedCoefficient
assert_compatible GUT.LiSixQuarkSemanticSeeds.seedCoefficient_reconstruct => Physics.LiSixQuarkSemanticSeeds.seedCoefficient_reconstruct
assert_compatible GUT.LiSixQuarkSemanticSeeds.seedCoordinates => Physics.LiSixQuarkSemanticSeeds.seedCoordinates
