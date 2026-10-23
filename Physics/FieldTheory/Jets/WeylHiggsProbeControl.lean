import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsProbeControl
import Physics.FieldTheory.Jets.WeylHiggsInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsProbeControl instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsProbeControl.Odd => Physics.WeylHiggsProbeControl.Odd,
  GUT.WeylHiggsProbeControl.P => Physics.WeylHiggsProbeControl.P,
  GUT.WeylHiggsProbeControl.augmentation => Physics.WeylHiggsProbeControl.augmentation,
  GUT.WeylHiggsProbeControl.augmentation.eq_1 => Physics.WeylHiggsProbeControl.augmentation.eq_1,
  GUT.WeylHiggsProbeControl.bosonEval => Physics.WeylHiggsProbeControl.bosonEval,
  GUT.WeylHiggsProbeControl.bosonEval.eq_1 => Physics.WeylHiggsProbeControl.bosonEval.eq_1,
  GUT.WeylHiggsProbeControl.bosonProbe => Physics.WeylHiggsProbeControl.bosonProbe,
  GUT.WeylHiggsProbeControl.bosonProbe.eq_1 => Physics.WeylHiggsProbeControl.bosonProbe.eq_1,
  GUT.WeylHiggsProbeControl.bosonValue => Physics.WeylHiggsProbeControl.bosonValue,
  GUT.WeylHiggsProbeControl.bosonValue.eq_1 => Physics.WeylHiggsProbeControl.bosonValue.eq_1,
  GUT.WeylHiggsProbeControl.candidate_value => Physics.WeylHiggsProbeControl.candidate_value,
  GUT.WeylHiggsProbeControl.divergence_value => Physics.WeylHiggsProbeControl.divergence_value,
  GUT.WeylHiggsProbeControl.oddProbe => Physics.WeylHiggsProbeControl.oddProbe,
  GUT.WeylHiggsProbeControl.oddProbe.eq_1 => Physics.WeylHiggsProbeControl.oddProbe.eq_1,
  GUT.WeylHiggsProbeControl.odd_pair => Physics.WeylHiggsProbeControl.odd_pair,
  GUT.WeylHiggsProbeControl.primitive => Physics.WeylHiggsProbeControl.primitive,
  GUT.WeylHiggsProbeControl.primitive.eq_1 => Physics.WeylHiggsProbeControl.primitive.eq_1,
  GUT.WeylHiggsProbeControl.probe => Physics.WeylHiggsProbeControl.probe,
  GUT.WeylHiggsProbeControl.probe_not_admitted => Physics.WeylHiggsProbeControl.probe_not_admitted,
  GUT.WeylHiggsProbeControl.probe_tmul => Physics.WeylHiggsProbeControl.probe_tmul,
  GUT.WeylHiggsProbeControl.raw_candidate_nonzero => Physics.WeylHiggsProbeControl.raw_candidate_nonzero
]

assert_compatible GUT.WeylHiggsProbeControl.Odd => Physics.WeylHiggsProbeControl.Odd
assert_compatible GUT.WeylHiggsProbeControl.P => Physics.WeylHiggsProbeControl.P
assert_compatible GUT.WeylHiggsProbeControl.augmentation => Physics.WeylHiggsProbeControl.augmentation
assert_compatible GUT.WeylHiggsProbeControl.augmentation.eq_1 => Physics.WeylHiggsProbeControl.augmentation.eq_1
assert_compatible GUT.WeylHiggsProbeControl.bosonEval => Physics.WeylHiggsProbeControl.bosonEval
assert_compatible GUT.WeylHiggsProbeControl.bosonEval.eq_1 => Physics.WeylHiggsProbeControl.bosonEval.eq_1
assert_compatible GUT.WeylHiggsProbeControl.bosonProbe => Physics.WeylHiggsProbeControl.bosonProbe
assert_compatible GUT.WeylHiggsProbeControl.bosonProbe.eq_1 => Physics.WeylHiggsProbeControl.bosonProbe.eq_1
assert_compatible GUT.WeylHiggsProbeControl.bosonValue => Physics.WeylHiggsProbeControl.bosonValue
assert_compatible GUT.WeylHiggsProbeControl.bosonValue.eq_1 => Physics.WeylHiggsProbeControl.bosonValue.eq_1
assert_compatible GUT.WeylHiggsProbeControl.candidate_value => Physics.WeylHiggsProbeControl.candidate_value
assert_compatible GUT.WeylHiggsProbeControl.divergence_value => Physics.WeylHiggsProbeControl.divergence_value
assert_compatible GUT.WeylHiggsProbeControl.oddProbe => Physics.WeylHiggsProbeControl.oddProbe
assert_compatible GUT.WeylHiggsProbeControl.oddProbe.eq_1 => Physics.WeylHiggsProbeControl.oddProbe.eq_1
assert_compatible GUT.WeylHiggsProbeControl.odd_pair => Physics.WeylHiggsProbeControl.odd_pair
assert_compatible GUT.WeylHiggsProbeControl.primitive => Physics.WeylHiggsProbeControl.primitive
assert_compatible GUT.WeylHiggsProbeControl.primitive.eq_1 => Physics.WeylHiggsProbeControl.primitive.eq_1
assert_compatible GUT.WeylHiggsProbeControl.probe => Physics.WeylHiggsProbeControl.probe
assert_compatible GUT.WeylHiggsProbeControl.probe_not_admitted => Physics.WeylHiggsProbeControl.probe_not_admitted
assert_compatible GUT.WeylHiggsProbeControl.probe_tmul => Physics.WeylHiggsProbeControl.probe_tmul
assert_compatible GUT.WeylHiggsProbeControl.raw_candidate_nonzero => Physics.WeylHiggsProbeControl.raw_candidate_nonzero
