import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveValues
import Physics.FieldTheory.Jets.WeylHiggsWaves
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveValues instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveValues.candidate => Physics.WeylHiggsWaveValues.candidate,
  GUT.WeylHiggsWaveValues.candidate_not_relation => Physics.WeylHiggsWaveValues.candidate_not_relation,
  GUT.WeylHiggsWaveValues.current => Physics.WeylHiggsWaveValues.current,
  GUT.WeylHiggsWaveValues.current_radius => Physics.WeylHiggsWaveValues.current_radius,
  GUT.WeylHiggsWaveValues.current_scalar => Physics.WeylHiggsWaveValues.current_scalar,
  GUT.WeylHiggsWaveValues.ev => Physics.WeylHiggsWaveValues.ev,
  GUT.WeylHiggsWaveValues.first => Physics.WeylHiggsWaveValues.first,
  GUT.WeylHiggsWaveValues.nonzero_value => Physics.WeylHiggsWaveValues.nonzero_value,
  GUT.WeylHiggsWaveValues.nullVector => Physics.WeylHiggsWaveValues.nullVector,
  GUT.WeylHiggsWaveValues.nullVector.eq_1 => Physics.WeylHiggsWaveValues.nullVector.eq_1,
  GUT.WeylHiggsWaveValues.nullVector_null => Physics.WeylHiggsWaveValues.nullVector_null,
  GUT.WeylHiggsWaveValues.radius => Physics.WeylHiggsWaveValues.radius,
  GUT.WeylHiggsWaves.probe.eq_1 => Physics.WeylHiggsWaves.probe.eq_1
]

assert_compatible GUT.WeylHiggsWaveValues.candidate => Physics.WeylHiggsWaveValues.candidate
assert_compatible GUT.WeylHiggsWaveValues.candidate_not_relation => Physics.WeylHiggsWaveValues.candidate_not_relation
assert_compatible GUT.WeylHiggsWaveValues.current => Physics.WeylHiggsWaveValues.current
assert_compatible GUT.WeylHiggsWaveValues.current_radius => Physics.WeylHiggsWaveValues.current_radius
assert_compatible GUT.WeylHiggsWaveValues.current_scalar => Physics.WeylHiggsWaveValues.current_scalar
assert_compatible GUT.WeylHiggsWaveValues.ev => Physics.WeylHiggsWaveValues.ev
assert_compatible GUT.WeylHiggsWaveValues.first => Physics.WeylHiggsWaveValues.first
assert_compatible GUT.WeylHiggsWaveValues.nonzero_value => Physics.WeylHiggsWaveValues.nonzero_value
assert_compatible GUT.WeylHiggsWaveValues.nullVector => Physics.WeylHiggsWaveValues.nullVector
assert_compatible GUT.WeylHiggsWaveValues.nullVector.eq_1 => Physics.WeylHiggsWaveValues.nullVector.eq_1
assert_compatible GUT.WeylHiggsWaveValues.nullVector_null => Physics.WeylHiggsWaveValues.nullVector_null
assert_compatible GUT.WeylHiggsWaveValues.radius => Physics.WeylHiggsWaveValues.radius
assert_compatible GUT.WeylHiggsWaves.probe.eq_1 => Physics.WeylHiggsWaves.probe.eq_1
