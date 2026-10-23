import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkQuotientConnection
import Physics.StandardModel.Operators.HeeckLeSixQuarkAssemblyBase
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkQuotientConnection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkAssemblyBase.top.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.top.eq_1,
  GUT.HeeckLeSixQuarkQuotientConnection.top_assemble => Physics.HeeckLeSixQuarkQuotientConnection.top_assemble,
  GUT.HeeckLeSixQuarkQuotientConnection.top_source1 => Physics.HeeckLeSixQuarkQuotientConnection.top_source1
]

assert_compatible GUT.HeeckLeSixQuarkAssemblyBase.top.eq_1 => Physics.HeeckLeSixQuarkAssemblyBase.top.eq_1
assert_compatible GUT.HeeckLeSixQuarkQuotientConnection.top_assemble => Physics.HeeckLeSixQuarkQuotientConnection.top_assemble
assert_compatible GUT.HeeckLeSixQuarkQuotientConnection.top_source1 => Physics.HeeckLeSixQuarkQuotientConnection.top_source1
