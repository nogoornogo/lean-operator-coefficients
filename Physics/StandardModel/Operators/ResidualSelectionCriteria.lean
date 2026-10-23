import Physics.StandardModel.Operators.Selection.ResidualSelectionCriteria
import Math.LinearAlgebra.SelectionCriteria
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.WeinbergSMInterface
import Physics.StandardModel.Operators.DipoleSMCoefficient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.ResidualSelectionCriteria instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ResidualSelectionCriteria.deltaBTwo => Physics.ResidualSelectionCriteria.deltaBTwo,
  GUT.ResidualSelectionCriteria.deltaLOne => Physics.ResidualSelectionCriteria.deltaLOne,
  GUT.ResidualSelectionCriteria.deltaLOne_forbidden_iff => Physics.ResidualSelectionCriteria.deltaLOne_forbidden_iff,
  GUT.ResidualSelectionCriteria.dipole => Physics.ResidualSelectionCriteria.dipole,
  GUT.ResidualSelectionCriteria.weinberg => Physics.ResidualSelectionCriteria.weinberg
]

assert_compatible GUT.ResidualSelectionCriteria.deltaBTwo => Physics.ResidualSelectionCriteria.deltaBTwo
assert_compatible GUT.ResidualSelectionCriteria.deltaLOne => Physics.ResidualSelectionCriteria.deltaLOne
assert_compatible GUT.ResidualSelectionCriteria.deltaLOne_forbidden_iff => Physics.ResidualSelectionCriteria.deltaLOne_forbidden_iff
assert_compatible GUT.ResidualSelectionCriteria.dipole => Physics.ResidualSelectionCriteria.dipole
assert_compatible GUT.ResidualSelectionCriteria.weinberg => Physics.ResidualSelectionCriteria.weinberg
