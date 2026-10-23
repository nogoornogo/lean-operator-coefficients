import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkCouplingConnection
import Physics.StandardModel.Operators.HeeckLeSixQuarkPairConnection
import Physics.StandardModel.Operators.HeeckLeSixQuarkQuotientConnection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkCouplingConnection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkCouplingConnection.residual_coupling => Physics.HeeckLeSixQuarkCouplingConnection.residual_coupling
]

assert_compatible GUT.HeeckLeSixQuarkCouplingConnection.residual_coupling => Physics.HeeckLeSixQuarkCouplingConnection.residual_coupling
