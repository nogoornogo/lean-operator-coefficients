import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance
import Math.LinearAlgebra.MediatorInheritance
import Physics.StandardModel.Operators.MediatorQque
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueMediatorInheritance.internal_eq => Physics.QqueMediatorInheritance.internal_eq,
  GUT.QqueMediatorInheritance.invariant => Physics.QqueMediatorInheritance.invariant,
  GUT.QqueMediatorInheritance.sector_eq => Physics.QqueMediatorInheritance.sector_eq
]

assert_compatible GUT.QqueMediatorInheritance.internal_eq => Physics.QqueMediatorInheritance.internal_eq
assert_compatible GUT.QqueMediatorInheritance.invariant => Physics.QqueMediatorInheritance.invariant
assert_compatible GUT.QqueMediatorInheritance.sector_eq => Physics.QqueMediatorInheritance.sector_eq
