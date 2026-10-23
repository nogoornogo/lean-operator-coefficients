import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenNegativeCoordinates
import Physics.StandardModel.Operators.BnvSevenNegativeTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenNegativeCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenNegativeCoordinates.Coordinates => Physics.BnvSevenNegativeCoordinates.Coordinates,
  GUT.BnvSevenNegativeCoordinates.forbidden_iff => Physics.BnvSevenNegativeCoordinates.forbidden_iff,
  GUT.BnvSevenNegativeCoordinates.mem_residualSpace_iff => Physics.BnvSevenNegativeCoordinates.mem_residualSpace_iff,
  GUT.BnvSevenNegativeCoordinates.ordered => Physics.BnvSevenNegativeCoordinates.ordered,
  GUT.BnvSevenNegativeCoordinates.orderedEquiv => Physics.BnvSevenNegativeCoordinates.orderedEquiv,
  GUT.BnvSevenNegativeCoordinates.orderedSynthesis => Physics.BnvSevenNegativeCoordinates.orderedSynthesis,
  GUT.BnvSevenNegativeCoordinates.orderedSynthesis.eq_1 => Physics.BnvSevenNegativeCoordinates.orderedSynthesis.eq_1,
  GUT.BnvSevenNegativeCoordinates.rawEquiv => Physics.BnvSevenNegativeCoordinates.rawEquiv,
  GUT.BnvSevenNegativeCoordinates.residualSpace => Physics.BnvSevenNegativeCoordinates.residualSpace,
  GUT.BnvSevenNegativeCoordinates.residualSpace.eq_1 => Physics.BnvSevenNegativeCoordinates.residualSpace.eq_1,
  GUT.BnvSevenNegativeCoordinates.tensorEquiv => Physics.BnvSevenNegativeCoordinates.tensorEquiv
]

assert_compatible GUT.BnvSevenNegativeCoordinates.Coordinates => Physics.BnvSevenNegativeCoordinates.Coordinates
assert_compatible GUT.BnvSevenNegativeCoordinates.forbidden_iff => Physics.BnvSevenNegativeCoordinates.forbidden_iff
assert_compatible GUT.BnvSevenNegativeCoordinates.mem_residualSpace_iff => Physics.BnvSevenNegativeCoordinates.mem_residualSpace_iff
assert_compatible GUT.BnvSevenNegativeCoordinates.ordered => Physics.BnvSevenNegativeCoordinates.ordered
assert_compatible GUT.BnvSevenNegativeCoordinates.orderedEquiv => Physics.BnvSevenNegativeCoordinates.orderedEquiv
assert_compatible GUT.BnvSevenNegativeCoordinates.orderedSynthesis => Physics.BnvSevenNegativeCoordinates.orderedSynthesis
assert_compatible GUT.BnvSevenNegativeCoordinates.orderedSynthesis.eq_1 => Physics.BnvSevenNegativeCoordinates.orderedSynthesis.eq_1
assert_compatible GUT.BnvSevenNegativeCoordinates.rawEquiv => Physics.BnvSevenNegativeCoordinates.rawEquiv
assert_compatible GUT.BnvSevenNegativeCoordinates.residualSpace => Physics.BnvSevenNegativeCoordinates.residualSpace
assert_compatible GUT.BnvSevenNegativeCoordinates.residualSpace.eq_1 => Physics.BnvSevenNegativeCoordinates.residualSpace.eq_1
assert_compatible GUT.BnvSevenNegativeCoordinates.tensorEquiv => Physics.BnvSevenNegativeCoordinates.tensorEquiv
