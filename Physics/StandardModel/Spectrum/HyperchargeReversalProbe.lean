import Physics.StandardModel.Spectrum.Representations.HyperchargeReversalProbe
import Physics.StandardModel.Spectrum.ExactSMSpectrum
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.HyperchargeReversalProbe instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HyperchargeReversalProbe.character_of_hypercharge => Physics.HyperchargeReversalProbe.character_of_hypercharge,
  GUT.HyperchargeReversalProbe.generation_character => Physics.HyperchargeReversalProbe.generation_character,
  GUT.HyperchargeReversalProbe.generation_probe_nonzero => Physics.HyperchargeReversalProbe.generation_probe_nonzero,
  GUT.HyperchargeReversalProbe.phase => Physics.HyperchargeReversalProbe.phase,
  GUT.HyperchargeReversalProbe.probe => Physics.HyperchargeReversalProbe.probe,
  GUT.HyperchargeReversalProbe.probe.eq_1 => Physics.HyperchargeReversalProbe.probe.eq_1
]

assert_compatible GUT.HyperchargeReversalProbe.character_of_hypercharge => Physics.HyperchargeReversalProbe.character_of_hypercharge
assert_compatible GUT.HyperchargeReversalProbe.generation_character => Physics.HyperchargeReversalProbe.generation_character
assert_compatible GUT.HyperchargeReversalProbe.generation_probe_nonzero => Physics.HyperchargeReversalProbe.generation_probe_nonzero
assert_compatible GUT.HyperchargeReversalProbe.phase => Physics.HyperchargeReversalProbe.phase
assert_compatible GUT.HyperchargeReversalProbe.probe => Physics.HyperchargeReversalProbe.probe
assert_compatible GUT.HyperchargeReversalProbe.probe.eq_1 => Physics.HyperchargeReversalProbe.probe.eq_1
