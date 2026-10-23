import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorTransport
import Math.LinearAlgebra.MediatorTransport
import Physics.StandardModel.Operators.QqueMediatorInheritance
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqueMediatorTransport.generated => Physics.QqueMediatorTransport.generated,
  GUT.QqueMediatorTransport.generated_eq => Physics.QqueMediatorTransport.generated_eq,
  GUT.QqueMediatorTransport.generated_ne_zero_iff => Physics.QqueMediatorTransport.generated_ne_zero_iff,
  GUT.QqueMediatorTransport.invariant => Physics.QqueMediatorTransport.invariant
]

assert_compatible GUT.QqueMediatorTransport.generated => Physics.QqueMediatorTransport.generated
assert_compatible GUT.QqueMediatorTransport.generated_eq => Physics.QqueMediatorTransport.generated_eq
assert_compatible GUT.QqueMediatorTransport.generated_ne_zero_iff => Physics.QqueMediatorTransport.generated_ne_zero_iff
assert_compatible GUT.QqueMediatorTransport.invariant => Physics.QqueMediatorTransport.invariant
