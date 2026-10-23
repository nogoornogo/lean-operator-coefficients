import Physics.FieldTheory.Spinor.Weyl.WeylCentralParity
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylCentralParity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylCentralParity.action_minus => Physics.WeylCentralParity.action_minus,
  GUT.WeylCentralParity.minusIdentity => Physics.WeylCentralParity.minusIdentity,
  GUT.WeylCentralParity.minusIdentity.eq_1 => Physics.WeylCentralParity.minusIdentity.eq_1
]

assert_compatible GUT.WeylCentralParity.action_minus => Physics.WeylCentralParity.action_minus
assert_compatible GUT.WeylCentralParity.minusIdentity => Physics.WeylCentralParity.minusIdentity
assert_compatible GUT.WeylCentralParity.minusIdentity.eq_1 => Physics.WeylCentralParity.minusIdentity.eq_1
