import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.FiniteInvariantFactor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourSameWeylCompleteness.Coefficient => Physics.FourSameWeylCompleteness.Coefficient,
  GUT.FourSameWeylCompleteness.action => Physics.FourSameWeylCompleteness.action,
  GUT.FourSameWeylCompleteness.action.eq_1 => Physics.FourSameWeylCompleteness.action.eq_1,
  GUT.FourSameWeylCompleteness.basisPairing => Physics.FourSameWeylCompleteness.basisPairing,
  GUT.FourSameWeylCompleteness.basisPairing.eq_1 => Physics.FourSameWeylCompleteness.basisPairing.eq_1,
  GUT.FourSameWeylCompleteness.basisPairing_formula => Physics.FourSameWeylCompleteness.basisPairing_formula,
  GUT.FourSameWeylCompleteness.basisPairing_probe => Physics.FourSameWeylCompleteness.basisPairing_probe,
  GUT.FourSameWeylCompleteness.coordinates => Physics.FourSameWeylCompleteness.coordinates,
  GUT.FourSameWeylCompleteness.eps_action => Physics.FourSameWeylCompleteness.eps_action,
  GUT.FourSameWeylCompleteness.flavorEquiv => Physics.FourSameWeylCompleteness.flavorEquiv,
  GUT.FourSameWeylCompleteness.formula => Physics.FourSameWeylCompleteness.formula,
  GUT.FourSameWeylCompleteness.pairing => Physics.FourSameWeylCompleteness.pairing,
  GUT.FourSameWeylCompleteness.pairing.eq_1 => Physics.FourSameWeylCompleteness.pairing.eq_1,
  GUT.FourSameWeylCompleteness.probe => Physics.FourSameWeylCompleteness.probe,
  GUT.FourSameWeylCompleteness.probe.eq_1 => Physics.FourSameWeylCompleteness.probe.eq_1,
  GUT.FourSameWeylCompleteness.representation => Physics.FourSameWeylCompleteness.representation,
  GUT.FourSameWeylCompleteness.representation.eq_1 => Physics.FourSameWeylCompleteness.representation.eq_1,
  GUT.FourSameWeylCompleteness.restrict_invariant => Physics.FourSameWeylCompleteness.restrict_invariant,
  GUT.FourSameWeylCompleteness.right_conjugate => Physics.FourSameWeylCompleteness.right_conjugate,
  GUT.FourSameWeylCompleteness.specialLinear => Physics.FourSameWeylCompleteness.specialLinear
]

assert_compatible GUT.FourSameWeylCompleteness.Coefficient => Physics.FourSameWeylCompleteness.Coefficient
assert_compatible GUT.FourSameWeylCompleteness.action => Physics.FourSameWeylCompleteness.action
assert_compatible GUT.FourSameWeylCompleteness.action.eq_1 => Physics.FourSameWeylCompleteness.action.eq_1
assert_compatible GUT.FourSameWeylCompleteness.basisPairing => Physics.FourSameWeylCompleteness.basisPairing
assert_compatible GUT.FourSameWeylCompleteness.basisPairing.eq_1 => Physics.FourSameWeylCompleteness.basisPairing.eq_1
assert_compatible GUT.FourSameWeylCompleteness.basisPairing_formula => Physics.FourSameWeylCompleteness.basisPairing_formula
assert_compatible GUT.FourSameWeylCompleteness.basisPairing_probe => Physics.FourSameWeylCompleteness.basisPairing_probe
assert_compatible GUT.FourSameWeylCompleteness.coordinates => Physics.FourSameWeylCompleteness.coordinates
assert_compatible GUT.FourSameWeylCompleteness.eps_action => Physics.FourSameWeylCompleteness.eps_action
assert_compatible GUT.FourSameWeylCompleteness.flavorEquiv => Physics.FourSameWeylCompleteness.flavorEquiv
assert_compatible GUT.FourSameWeylCompleteness.formula => Physics.FourSameWeylCompleteness.formula
assert_compatible GUT.FourSameWeylCompleteness.pairing => Physics.FourSameWeylCompleteness.pairing
assert_compatible GUT.FourSameWeylCompleteness.pairing.eq_1 => Physics.FourSameWeylCompleteness.pairing.eq_1
assert_compatible GUT.FourSameWeylCompleteness.probe => Physics.FourSameWeylCompleteness.probe
assert_compatible GUT.FourSameWeylCompleteness.probe.eq_1 => Physics.FourSameWeylCompleteness.probe.eq_1
assert_compatible GUT.FourSameWeylCompleteness.representation => Physics.FourSameWeylCompleteness.representation
assert_compatible GUT.FourSameWeylCompleteness.representation.eq_1 => Physics.FourSameWeylCompleteness.representation.eq_1
assert_compatible GUT.FourSameWeylCompleteness.restrict_invariant => Physics.FourSameWeylCompleteness.restrict_invariant
assert_compatible GUT.FourSameWeylCompleteness.right_conjugate => Physics.FourSameWeylCompleteness.right_conjugate
assert_compatible GUT.FourSameWeylCompleteness.specialLinear => Physics.FourSameWeylCompleteness.specialLinear
