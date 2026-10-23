import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraPhysicalSource
import Physics.StandardModel.Operators.DevMohapatraConnection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraPhysicalSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraPhysicalSource.Field => Physics.DevMohapatraPhysicalSource.Field,
  GUT.DevMohapatraPhysicalSource.P => Physics.DevMohapatraPhysicalSource.P,
  GUT.DevMohapatraPhysicalSource.coefficient => Physics.DevMohapatraPhysicalSource.coefficient,
  GUT.DevMohapatraPhysicalSource.domain => Physics.DevMohapatraPhysicalSource.domain,
  GUT.DevMohapatraPhysicalSource.evaluation => Physics.DevMohapatraPhysicalSource.evaluation,
  GUT.DevMohapatraPhysicalSource.instAddCommGroupProdField => Physics.DevMohapatraPhysicalSource.instAddCommGroupProdField,
  GUT.DevMohapatraPhysicalSource.instZeroDomain => Physics.DevMohapatraPhysicalSource.instZeroDomain,
  GUT.DevMohapatraPhysicalSource.nonzero => Physics.DevMohapatraPhysicalSource.nonzero,
  GUT.DevMohapatraPhysicalSource.reorder => Physics.DevMohapatraPhysicalSource.reorder,
  GUT.DevMohapatraPhysicalSource.rho => Physics.DevMohapatraPhysicalSource.rho,
  GUT.DevMohapatraPhysicalSource.satisfies => Physics.DevMohapatraPhysicalSource.satisfies,
  GUT.DevMohapatraPhysicalSource.selected => Physics.DevMohapatraPhysicalSource.selected,
  GUT.DevMohapatraPhysicalSource.source => Physics.DevMohapatraPhysicalSource.source
]

assert_compatible GUT.DevMohapatraPhysicalSource.Field => Physics.DevMohapatraPhysicalSource.Field
assert_compatible GUT.DevMohapatraPhysicalSource.P => Physics.DevMohapatraPhysicalSource.P
assert_compatible GUT.DevMohapatraPhysicalSource.coefficient => Physics.DevMohapatraPhysicalSource.coefficient
assert_compatible GUT.DevMohapatraPhysicalSource.domain => Physics.DevMohapatraPhysicalSource.domain
assert_compatible GUT.DevMohapatraPhysicalSource.evaluation => Physics.DevMohapatraPhysicalSource.evaluation
assert_compatible GUT.DevMohapatraPhysicalSource.instAddCommGroupProdField => Physics.DevMohapatraPhysicalSource.instAddCommGroupProdField
assert_compatible GUT.DevMohapatraPhysicalSource.instZeroDomain => Physics.DevMohapatraPhysicalSource.instZeroDomain
assert_compatible GUT.DevMohapatraPhysicalSource.nonzero => Physics.DevMohapatraPhysicalSource.nonzero
assert_compatible GUT.DevMohapatraPhysicalSource.reorder => Physics.DevMohapatraPhysicalSource.reorder
assert_compatible GUT.DevMohapatraPhysicalSource.rho => Physics.DevMohapatraPhysicalSource.rho
assert_compatible GUT.DevMohapatraPhysicalSource.satisfies => Physics.DevMohapatraPhysicalSource.satisfies
assert_compatible GUT.DevMohapatraPhysicalSource.selected => Physics.DevMohapatraPhysicalSource.selected
assert_compatible GUT.DevMohapatraPhysicalSource.source => Physics.DevMohapatraPhysicalSource.source
