import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenNegativeTransport
import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Operators.BnvSevenLocalTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenNegativeTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenNegativeTransport.Index => Physics.BnvSevenNegativeTransport.Index,
  GUT.BnvSevenNegativeTransport.flavorAlongEquiv => Physics.BnvSevenNegativeTransport.flavorAlongEquiv,
  GUT.BnvSevenNegativeTransport.flavorEquiv => Physics.BnvSevenNegativeTransport.flavorEquiv,
  GUT.BnvSevenNegativeTransport.invariantEquiv => Physics.BnvSevenNegativeTransport.invariantEquiv,
  GUT.BnvSevenNegativeTransport.localEquiv => Physics.BnvSevenNegativeTransport.localEquiv,
  GUT.BnvSevenNegativeTransport.opposite_pattern => Physics.BnvSevenNegativeTransport.opposite_pattern,
  GUT.BnvSevenNegativeTransport.opposite_scalar => Physics.BnvSevenNegativeTransport.opposite_scalar,
  GUT.BnvSevenNegativeTransport.pairing => Physics.BnvSevenNegativeTransport.pairing,
  GUT.BnvSevenNegativeTransport.pairing_probe => Physics.BnvSevenNegativeTransport.pairing_probe,
  GUT.BnvSevenNegativeTransport.pattern => Physics.BnvSevenNegativeTransport.pattern,
  GUT.BnvSevenNegativeTransport.positive => Physics.BnvSevenNegativeTransport.positive,
  GUT.BnvSevenNegativeTransport.probe => Physics.BnvSevenNegativeTransport.probe,
  GUT.BnvSevenNegativeTransport.reconstruction => Physics.BnvSevenNegativeTransport.reconstruction,
  GUT.BnvSevenNegativeTransport.relabel => Physics.BnvSevenNegativeTransport.relabel,
  GUT.BnvSevenNegativeTransport.restrictEquiv => Physics.BnvSevenNegativeTransport.restrictEquiv,
  GUT.BnvSevenNegativeTransport.scalar => Physics.BnvSevenNegativeTransport.scalar
]

assert_compatible GUT.BnvSevenNegativeTransport.Index => Physics.BnvSevenNegativeTransport.Index
assert_compatible GUT.BnvSevenNegativeTransport.flavorAlongEquiv => Physics.BnvSevenNegativeTransport.flavorAlongEquiv
assert_compatible GUT.BnvSevenNegativeTransport.flavorEquiv => Physics.BnvSevenNegativeTransport.flavorEquiv
assert_compatible GUT.BnvSevenNegativeTransport.invariantEquiv => Physics.BnvSevenNegativeTransport.invariantEquiv
assert_compatible GUT.BnvSevenNegativeTransport.localEquiv => Physics.BnvSevenNegativeTransport.localEquiv
assert_compatible GUT.BnvSevenNegativeTransport.opposite_pattern => Physics.BnvSevenNegativeTransport.opposite_pattern
assert_compatible GUT.BnvSevenNegativeTransport.opposite_scalar => Physics.BnvSevenNegativeTransport.opposite_scalar
assert_compatible GUT.BnvSevenNegativeTransport.pairing => Physics.BnvSevenNegativeTransport.pairing
assert_compatible GUT.BnvSevenNegativeTransport.pairing_probe => Physics.BnvSevenNegativeTransport.pairing_probe
assert_compatible GUT.BnvSevenNegativeTransport.pattern => Physics.BnvSevenNegativeTransport.pattern
assert_compatible GUT.BnvSevenNegativeTransport.positive => Physics.BnvSevenNegativeTransport.positive
assert_compatible GUT.BnvSevenNegativeTransport.probe => Physics.BnvSevenNegativeTransport.probe
assert_compatible GUT.BnvSevenNegativeTransport.reconstruction => Physics.BnvSevenNegativeTransport.reconstruction
assert_compatible GUT.BnvSevenNegativeTransport.relabel => Physics.BnvSevenNegativeTransport.relabel
assert_compatible GUT.BnvSevenNegativeTransport.restrictEquiv => Physics.BnvSevenNegativeTransport.restrictEquiv
assert_compatible GUT.BnvSevenNegativeTransport.scalar => Physics.BnvSevenNegativeTransport.scalar
