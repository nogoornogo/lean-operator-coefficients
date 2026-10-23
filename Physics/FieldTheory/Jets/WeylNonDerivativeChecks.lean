import Physics.FieldTheory.Jets.Weyl.Equations.WeylNonDerivativeChecks
import Math.RepresentationTheory.NonDerivativeInputChecks
import Physics.FieldTheory.Jets.LorentzJetIBP
import Physics.FieldTheory.Spinor.WeylCentralParity
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylNonDerivativeChecks instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylNonDerivativeChecks.bosons => Physics.WeylNonDerivativeChecks.bosons,
  GUT.WeylNonDerivativeChecks.directions => Physics.WeylNonDerivativeChecks.directions,
  GUT.WeylNonDerivativeChecks.epsilon_invariant => Physics.WeylNonDerivativeChecks.epsilon_invariant,
  GUT.WeylNonDerivativeChecks.fermions => Physics.WeylNonDerivativeChecks.fermions,
  GUT.WeylNonDerivativeChecks.field_minus => Physics.WeylNonDerivativeChecks.field_minus,
  GUT.WeylNonDerivativeChecks.instAddCommGroupOriginalFinOfNatNatUnit_physics => Physics.WeylNonDerivativeChecks.instAddCommGroupOriginalFinOfNatNatUnit_physics,
  GUT.WeylNonDerivativeChecks.instModuleComplexOriginalFinOfNatNatUnit_physics => Physics.WeylNonDerivativeChecks.instModuleComplexOriginalFinOfNatNatUnit_physics,
  GUT.WeylNonDerivativeChecks.inverse => Physics.WeylNonDerivativeChecks.inverse,
  GUT.WeylNonDerivativeChecks.nonzero => Physics.WeylNonDerivativeChecks.nonzero,
  GUT.WeylNonDerivativeChecks.normalized => Physics.WeylNonDerivativeChecks.normalized,
  GUT.WeylNonDerivativeChecks.odd_forbidden => Physics.WeylNonDerivativeChecks.odd_forbidden,
  GUT.WeylNonDerivativeChecks.old => Physics.WeylNonDerivativeChecks.old,
  GUT.WeylNonDerivativeChecks.swap_value => Physics.WeylNonDerivativeChecks.swap_value,
  GUT.WeylNonDerivativeChecks.unified => Physics.WeylNonDerivativeChecks.unified,
  GUT.WeylNonDerivativeChecks.unified_odd_forbidden => Physics.WeylNonDerivativeChecks.unified_odd_forbidden,
  GUT.WeylNonDerivativeChecks.value => Physics.WeylNonDerivativeChecks.value,
  GUT.WeylNonDerivativeChecks.value.eq_1 => Physics.WeylNonDerivativeChecks.value.eq_1,
  GUT.WeylNonDerivativeChecks.value_pure => Physics.WeylNonDerivativeChecks.value_pure
]

assert_compatible GUT.WeylNonDerivativeChecks.bosons => Physics.WeylNonDerivativeChecks.bosons
assert_compatible GUT.WeylNonDerivativeChecks.directions => Physics.WeylNonDerivativeChecks.directions
assert_compatible GUT.WeylNonDerivativeChecks.epsilon_invariant => Physics.WeylNonDerivativeChecks.epsilon_invariant
assert_compatible GUT.WeylNonDerivativeChecks.fermions => Physics.WeylNonDerivativeChecks.fermions
assert_compatible GUT.WeylNonDerivativeChecks.field_minus => Physics.WeylNonDerivativeChecks.field_minus
assert_compatible GUT.WeylNonDerivativeChecks.instAddCommGroupOriginalFinOfNatNatUnit_physics => Physics.WeylNonDerivativeChecks.instAddCommGroupOriginalFinOfNatNatUnit_physics
assert_compatible GUT.WeylNonDerivativeChecks.instModuleComplexOriginalFinOfNatNatUnit_physics => Physics.WeylNonDerivativeChecks.instModuleComplexOriginalFinOfNatNatUnit_physics
assert_compatible GUT.WeylNonDerivativeChecks.inverse => Physics.WeylNonDerivativeChecks.inverse
assert_compatible GUT.WeylNonDerivativeChecks.nonzero => Physics.WeylNonDerivativeChecks.nonzero
assert_compatible GUT.WeylNonDerivativeChecks.normalized => Physics.WeylNonDerivativeChecks.normalized
assert_compatible GUT.WeylNonDerivativeChecks.odd_forbidden => Physics.WeylNonDerivativeChecks.odd_forbidden
assert_compatible GUT.WeylNonDerivativeChecks.old => Physics.WeylNonDerivativeChecks.old
assert_compatible GUT.WeylNonDerivativeChecks.swap_value => Physics.WeylNonDerivativeChecks.swap_value
assert_compatible GUT.WeylNonDerivativeChecks.unified => Physics.WeylNonDerivativeChecks.unified
assert_compatible GUT.WeylNonDerivativeChecks.unified_odd_forbidden => Physics.WeylNonDerivativeChecks.unified_odd_forbidden
assert_compatible GUT.WeylNonDerivativeChecks.value => Physics.WeylNonDerivativeChecks.value
assert_compatible GUT.WeylNonDerivativeChecks.value.eq_1 => Physics.WeylNonDerivativeChecks.value.eq_1
assert_compatible GUT.WeylNonDerivativeChecks.value_pure => Physics.WeylNonDerivativeChecks.value_pure
