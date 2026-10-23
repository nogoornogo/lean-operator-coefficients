import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenSignedCoordinates
import Physics.StandardModel.Operators.BnvSevenResidualCoordinates
import Physics.StandardModel.Operators.BnvSevenNegativeCoordinates
import Physics.StandardModel.Operators.BnvSevenFamilyDecomposition
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenSignedCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenSignedCoordinates.Factor => Physics.BnvSevenSignedCoordinates.Factor,
  GUT.BnvSevenSignedCoordinates.equiv => Physics.BnvSevenSignedCoordinates.equiv,
  GUT.BnvSevenSignedCoordinates.factorEquiv => Physics.BnvSevenSignedCoordinates.factorEquiv,
  GUT.BnvSevenSignedCoordinates.forbidden_iff => Physics.BnvSevenSignedCoordinates.forbidden_iff,
  GUT.BnvSevenSignedCoordinates.instAddCommGroupFactor => Physics.BnvSevenSignedCoordinates.instAddCommGroupFactor,
  GUT.BnvSevenSignedCoordinates.instModuleComplexFactor => Physics.BnvSevenSignedCoordinates.instModuleComplexFactor,
  GUT.BnvSevenSignedCoordinates.nonzero_iff => Physics.BnvSevenSignedCoordinates.nonzero_iff
]

assert_compatible GUT.BnvSevenSignedCoordinates.Factor => Physics.BnvSevenSignedCoordinates.Factor
assert_compatible GUT.BnvSevenSignedCoordinates.equiv => Physics.BnvSevenSignedCoordinates.equiv
assert_compatible GUT.BnvSevenSignedCoordinates.factorEquiv => Physics.BnvSevenSignedCoordinates.factorEquiv
assert_compatible GUT.BnvSevenSignedCoordinates.forbidden_iff => Physics.BnvSevenSignedCoordinates.forbidden_iff
assert_compatible GUT.BnvSevenSignedCoordinates.instAddCommGroupFactor => Physics.BnvSevenSignedCoordinates.instAddCommGroupFactor
assert_compatible GUT.BnvSevenSignedCoordinates.instModuleComplexFactor => Physics.BnvSevenSignedCoordinates.instModuleComplexFactor
assert_compatible GUT.BnvSevenSignedCoordinates.nonzero_iff => Physics.BnvSevenSignedCoordinates.nonzero_iff
