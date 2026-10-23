import Physics.StandardModel.Operators.BaryonOne.Inputs.FourWeakWeylCompleteness
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.FourWeakWeylCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourWeakWeylCompleteness.Coefficient => Physics.FourWeakWeylCompleteness.Coefficient,
  GUT.FourWeakWeylCompleteness.coordinates => Physics.FourWeakWeylCompleteness.coordinates,
  GUT.FourWeakWeylCompleteness.pairing => Physics.FourWeakWeylCompleteness.pairing,
  GUT.FourWeakWeylCompleteness.pairing_probe => Physics.FourWeakWeylCompleteness.pairing_probe,
  GUT.FourWeakWeylCompleteness.probe => Physics.FourWeakWeylCompleteness.probe,
  GUT.FourWeakWeylCompleteness.reconstruction => Physics.FourWeakWeylCompleteness.reconstruction,
  GUT.FourWeakWeylCompleteness.representation => Physics.FourWeakWeylCompleteness.representation,
  GUT.FourWeakWeylCompleteness.weakPairing => Physics.FourWeakWeylCompleteness.weakPairing,
  GUT.FourWeakWeylCompleteness.weakPairing.eq_1 => Physics.FourWeakWeylCompleteness.weakPairing.eq_1,
  GUT.FourWeakWeylCompleteness.weakRepresentation => Physics.FourWeakWeylCompleteness.weakRepresentation,
  GUT.FourWeakWeylCompleteness.weak_formula => Physics.FourWeakWeylCompleteness.weak_formula,
  GUT.FourWeakWeylCompleteness.weak_probe => Physics.FourWeakWeylCompleteness.weak_probe
]

assert_compatible GUT.FourWeakWeylCompleteness.Coefficient => Physics.FourWeakWeylCompleteness.Coefficient
assert_compatible GUT.FourWeakWeylCompleteness.coordinates => Physics.FourWeakWeylCompleteness.coordinates
assert_compatible GUT.FourWeakWeylCompleteness.pairing => Physics.FourWeakWeylCompleteness.pairing
assert_compatible GUT.FourWeakWeylCompleteness.pairing_probe => Physics.FourWeakWeylCompleteness.pairing_probe
assert_compatible GUT.FourWeakWeylCompleteness.probe => Physics.FourWeakWeylCompleteness.probe
assert_compatible GUT.FourWeakWeylCompleteness.reconstruction => Physics.FourWeakWeylCompleteness.reconstruction
assert_compatible GUT.FourWeakWeylCompleteness.representation => Physics.FourWeakWeylCompleteness.representation
assert_compatible GUT.FourWeakWeylCompleteness.weakPairing => Physics.FourWeakWeylCompleteness.weakPairing
assert_compatible GUT.FourWeakWeylCompleteness.weakPairing.eq_1 => Physics.FourWeakWeylCompleteness.weakPairing.eq_1
assert_compatible GUT.FourWeakWeylCompleteness.weakRepresentation => Physics.FourWeakWeylCompleteness.weakRepresentation
assert_compatible GUT.FourWeakWeylCompleteness.weak_formula => Physics.FourWeakWeylCompleteness.weak_formula
assert_compatible GUT.FourWeakWeylCompleteness.weak_probe => Physics.FourWeakWeylCompleteness.weak_probe
