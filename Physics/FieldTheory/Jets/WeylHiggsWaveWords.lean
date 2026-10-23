import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveWords
import Physics.FieldTheory.Jets.WeylHiggsEvenValue
import Physics.FieldTheory.Jets.WeylHiggsWaveSum
import Math.RepresentationTheory.MarkedFieldPairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveWords instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveWords.boson_value => Physics.WeylHiggsWaveWords.boson_value,
  GUT.WeylHiggsWaveWords.color => Physics.WeylHiggsWaveWords.color,
  GUT.WeylHiggsWaveWords.color.eq_1 => Physics.WeylHiggsWaveWords.color.eq_1,
  GUT.WeylHiggsWaveWords.color_pairing => Physics.WeylHiggsWaveWords.color_pairing,
  GUT.WeylHiggsWaveWords.delta => Physics.WeylHiggsWaveWords.delta,
  GUT.WeylHiggsWaveWords.delta.eq_1 => Physics.WeylHiggsWaveWords.delta.eq_1,
  GUT.WeylHiggsWaveWords.delta_left => Physics.WeylHiggsWaveWords.delta_left,
  GUT.WeylHiggsWaveWords.delta_same => Physics.WeylHiggsWaveWords.delta_same,
  GUT.WeylHiggsWaveWords.functional_positive_odd => Physics.WeylHiggsWaveWords.functional_positive_odd,
  GUT.WeylHiggsWaveWords.functional_scalar_left => Physics.WeylHiggsWaveWords.functional_scalar_left,
  GUT.WeylHiggsWaveWords.functional_scalar_same => Physics.WeylHiggsWaveWords.functional_scalar_same,
  GUT.WeylHiggsWaveWords.instAddCommGroupA_physics => Physics.WeylHiggsWaveWords.instAddCommGroupA_physics,
  GUT.WeylHiggsWaveWords.instModuleComplexA_physics => Physics.WeylHiggsWaveWords.instModuleComplexA_physics,
  GUT.WeylHiggsWaveWords.instRingA_physics => Physics.WeylHiggsWaveWords.instRingA_physics,
  GUT.WeylHiggsWaveWords.probe_positive_odd => Physics.WeylHiggsWaveWords.probe_positive_odd,
  GUT.WeylHiggsWaveWords.probe_scalar => Physics.WeylHiggsWaveWords.probe_scalar,
  GUT.WeylHiggsWaveWords.quartic => Physics.WeylHiggsWaveWords.quartic,
  GUT.WeylHiggsWaveWords.quartic.eq_1 => Physics.WeylHiggsWaveWords.quartic.eq_1
]

assert_compatible GUT.WeylHiggsWaveWords.boson_value => Physics.WeylHiggsWaveWords.boson_value
assert_compatible GUT.WeylHiggsWaveWords.color => Physics.WeylHiggsWaveWords.color
assert_compatible GUT.WeylHiggsWaveWords.color.eq_1 => Physics.WeylHiggsWaveWords.color.eq_1
assert_compatible GUT.WeylHiggsWaveWords.color_pairing => Physics.WeylHiggsWaveWords.color_pairing
assert_compatible GUT.WeylHiggsWaveWords.delta => Physics.WeylHiggsWaveWords.delta
assert_compatible GUT.WeylHiggsWaveWords.delta.eq_1 => Physics.WeylHiggsWaveWords.delta.eq_1
assert_compatible GUT.WeylHiggsWaveWords.delta_left => Physics.WeylHiggsWaveWords.delta_left
assert_compatible GUT.WeylHiggsWaveWords.delta_same => Physics.WeylHiggsWaveWords.delta_same
assert_compatible GUT.WeylHiggsWaveWords.functional_positive_odd => Physics.WeylHiggsWaveWords.functional_positive_odd
assert_compatible GUT.WeylHiggsWaveWords.functional_scalar_left => Physics.WeylHiggsWaveWords.functional_scalar_left
assert_compatible GUT.WeylHiggsWaveWords.functional_scalar_same => Physics.WeylHiggsWaveWords.functional_scalar_same
assert_compatible GUT.WeylHiggsWaveWords.instAddCommGroupA_physics => Physics.WeylHiggsWaveWords.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsWaveWords.instModuleComplexA_physics => Physics.WeylHiggsWaveWords.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsWaveWords.instRingA_physics => Physics.WeylHiggsWaveWords.instRingA_physics
assert_compatible GUT.WeylHiggsWaveWords.probe_positive_odd => Physics.WeylHiggsWaveWords.probe_positive_odd
assert_compatible GUT.WeylHiggsWaveWords.probe_scalar => Physics.WeylHiggsWaveWords.probe_scalar
assert_compatible GUT.WeylHiggsWaveWords.quartic => Physics.WeylHiggsWaveWords.quartic
assert_compatible GUT.WeylHiggsWaveWords.quartic.eq_1 => Physics.WeylHiggsWaveWords.quartic.eq_1
