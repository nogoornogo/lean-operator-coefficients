import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlLocalCompleteness
import Physics.StandardModel.Operators.FourWeakWeylCompleteness
import Physics.StandardModel.Gauge.SMEpsilonUniqueness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlLocalCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlLocalCompleteness.Coefficient => Physics.QqqlLocalCompleteness.Coefficient,
  GUT.QqqlLocalCompleteness.ColorGroup => Physics.QqqlLocalCompleteness.ColorGroup,
  GUT.QqqlLocalCompleteness.LocalGroup => Physics.QqqlLocalCompleteness.LocalGroup,
  GUT.QqqlLocalCompleteness.colorPairing => Physics.QqqlLocalCompleteness.colorPairing,
  GUT.QqqlLocalCompleteness.colorPairing.eq_1 => Physics.QqqlLocalCompleteness.colorPairing.eq_1,
  GUT.QqqlLocalCompleteness.colorProbe => Physics.QqqlLocalCompleteness.colorProbe,
  GUT.QqqlLocalCompleteness.colorProbe.eq_1 => Physics.QqqlLocalCompleteness.colorProbe.eq_1,
  GUT.QqqlLocalCompleteness.colorRepresentation => Physics.QqqlLocalCompleteness.colorRepresentation,
  GUT.QqqlLocalCompleteness.color_normalized => Physics.QqqlLocalCompleteness.color_normalized,
  GUT.QqqlLocalCompleteness.color_unique => Physics.QqqlLocalCompleteness.color_unique,
  GUT.QqqlLocalCompleteness.flavor => Physics.QqqlLocalCompleteness.flavor,
  GUT.QqqlLocalCompleteness.homEquiv => Physics.QqqlLocalCompleteness.homEquiv,
  GUT.QqqlLocalCompleteness.pairing => Physics.QqqlLocalCompleteness.pairing,
  GUT.QqqlLocalCompleteness.pairing_probe => Physics.QqqlLocalCompleteness.pairing_probe,
  GUT.QqqlLocalCompleteness.probe => Physics.QqqlLocalCompleteness.probe,
  GUT.QqqlLocalCompleteness.reconstruction => Physics.QqqlLocalCompleteness.reconstruction,
  GUT.QqqlLocalCompleteness.representation => Physics.QqqlLocalCompleteness.representation
]

assert_compatible GUT.QqqlLocalCompleteness.Coefficient => Physics.QqqlLocalCompleteness.Coefficient
assert_compatible GUT.QqqlLocalCompleteness.ColorGroup => Physics.QqqlLocalCompleteness.ColorGroup
assert_compatible GUT.QqqlLocalCompleteness.LocalGroup => Physics.QqqlLocalCompleteness.LocalGroup
assert_compatible GUT.QqqlLocalCompleteness.colorPairing => Physics.QqqlLocalCompleteness.colorPairing
assert_compatible GUT.QqqlLocalCompleteness.colorPairing.eq_1 => Physics.QqqlLocalCompleteness.colorPairing.eq_1
assert_compatible GUT.QqqlLocalCompleteness.colorProbe => Physics.QqqlLocalCompleteness.colorProbe
assert_compatible GUT.QqqlLocalCompleteness.colorProbe.eq_1 => Physics.QqqlLocalCompleteness.colorProbe.eq_1
assert_compatible GUT.QqqlLocalCompleteness.colorRepresentation => Physics.QqqlLocalCompleteness.colorRepresentation
assert_compatible GUT.QqqlLocalCompleteness.color_normalized => Physics.QqqlLocalCompleteness.color_normalized
assert_compatible GUT.QqqlLocalCompleteness.color_unique => Physics.QqqlLocalCompleteness.color_unique
assert_compatible GUT.QqqlLocalCompleteness.flavor => Physics.QqqlLocalCompleteness.flavor
assert_compatible GUT.QqqlLocalCompleteness.homEquiv => Physics.QqqlLocalCompleteness.homEquiv
assert_compatible GUT.QqqlLocalCompleteness.pairing => Physics.QqqlLocalCompleteness.pairing
assert_compatible GUT.QqqlLocalCompleteness.pairing_probe => Physics.QqqlLocalCompleteness.pairing_probe
assert_compatible GUT.QqqlLocalCompleteness.probe => Physics.QqqlLocalCompleteness.probe
assert_compatible GUT.QqqlLocalCompleteness.reconstruction => Physics.QqqlLocalCompleteness.reconstruction
assert_compatible GUT.QqqlLocalCompleteness.representation => Physics.QqqlLocalCompleteness.representation
