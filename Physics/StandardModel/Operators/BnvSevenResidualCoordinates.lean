import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenResidualCoordinates
import Physics.StandardModel.Operators.BnvSevenLocalTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenResidualCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenFieldTensor.tensorSector.eq_1 => Physics.BnvSevenFieldTensor.tensorSector.eq_1,
  GUT.BnvSevenResidualCoordinates.Coordinates => Physics.BnvSevenResidualCoordinates.Coordinates,
  GUT.BnvSevenResidualCoordinates.familyEquiv => Physics.BnvSevenResidualCoordinates.familyEquiv,
  GUT.BnvSevenResidualCoordinates.forbidden_iff => Physics.BnvSevenResidualCoordinates.forbidden_iff,
  GUT.BnvSevenResidualCoordinates.mem_residualSpace_iff => Physics.BnvSevenResidualCoordinates.mem_residualSpace_iff,
  GUT.BnvSevenResidualCoordinates.nonzero_iff => Physics.BnvSevenResidualCoordinates.nonzero_iff,
  GUT.BnvSevenResidualCoordinates.orderedEquiv => Physics.BnvSevenResidualCoordinates.orderedEquiv,
  GUT.BnvSevenResidualCoordinates.orderedSynthesis => Physics.BnvSevenResidualCoordinates.orderedSynthesis,
  GUT.BnvSevenResidualCoordinates.orderedSynthesis.eq_1 => Physics.BnvSevenResidualCoordinates.orderedSynthesis.eq_1,
  GUT.BnvSevenResidualCoordinates.rawEquiv => Physics.BnvSevenResidualCoordinates.rawEquiv,
  GUT.BnvSevenResidualCoordinates.residualSpace => Physics.BnvSevenResidualCoordinates.residualSpace,
  GUT.BnvSevenResidualCoordinates.residualSpace.eq_1 => Physics.BnvSevenResidualCoordinates.residualSpace.eq_1,
  GUT.BnvSevenResidualCoordinates.tensorEquiv => Physics.BnvSevenResidualCoordinates.tensorEquiv
]

assert_compatible GUT.BnvSevenFieldTensor.tensorSector.eq_1 => Physics.BnvSevenFieldTensor.tensorSector.eq_1
assert_compatible GUT.BnvSevenResidualCoordinates.Coordinates => Physics.BnvSevenResidualCoordinates.Coordinates
assert_compatible GUT.BnvSevenResidualCoordinates.familyEquiv => Physics.BnvSevenResidualCoordinates.familyEquiv
assert_compatible GUT.BnvSevenResidualCoordinates.forbidden_iff => Physics.BnvSevenResidualCoordinates.forbidden_iff
assert_compatible GUT.BnvSevenResidualCoordinates.mem_residualSpace_iff => Physics.BnvSevenResidualCoordinates.mem_residualSpace_iff
assert_compatible GUT.BnvSevenResidualCoordinates.nonzero_iff => Physics.BnvSevenResidualCoordinates.nonzero_iff
assert_compatible GUT.BnvSevenResidualCoordinates.orderedEquiv => Physics.BnvSevenResidualCoordinates.orderedEquiv
assert_compatible GUT.BnvSevenResidualCoordinates.orderedSynthesis => Physics.BnvSevenResidualCoordinates.orderedSynthesis
assert_compatible GUT.BnvSevenResidualCoordinates.orderedSynthesis.eq_1 => Physics.BnvSevenResidualCoordinates.orderedSynthesis.eq_1
assert_compatible GUT.BnvSevenResidualCoordinates.rawEquiv => Physics.BnvSevenResidualCoordinates.rawEquiv
assert_compatible GUT.BnvSevenResidualCoordinates.residualSpace => Physics.BnvSevenResidualCoordinates.residualSpace
assert_compatible GUT.BnvSevenResidualCoordinates.residualSpace.eq_1 => Physics.BnvSevenResidualCoordinates.residualSpace.eq_1
assert_compatible GUT.BnvSevenResidualCoordinates.tensorEquiv => Physics.BnvSevenResidualCoordinates.tensorEquiv
