import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaves
import Physics.FieldTheory.Jets.WeylHiggsSelection
import Physics.FieldTheory.Jets.HiggsQuarticFourWaves
import Math.Algebra.MixedFourWaveEvaluation
import Math.RepresentationTheory.ColoredWavePairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaves instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaves.Odd0 => Physics.WeylHiggsWaves.Odd0,
  GUT.WeylHiggsWaves.annihilates => Physics.WeylHiggsWaves.annihilates,
  GUT.WeylHiggsWaves.augmentation => Physics.WeylHiggsWaves.augmentation,
  GUT.WeylHiggsWaves.augmentation.eq_1 => Physics.WeylHiggsWaves.augmentation.eq_1,
  GUT.WeylHiggsWaves.component_zero => Physics.WeylHiggsWaves.component_zero,
  GUT.WeylHiggsWaves.conserving => Physics.WeylHiggsWaves.conserving,
  GUT.WeylHiggsWaves.evaluation => Physics.WeylHiggsWaves.evaluation,
  GUT.WeylHiggsWaves.momenta => Physics.WeylHiggsWaves.momenta,
  GUT.WeylHiggsWaves.momenta.eq_1 => Physics.WeylHiggsWaves.momenta.eq_1,
  GUT.WeylHiggsWaves.null => Physics.WeylHiggsWaves.null,
  GUT.WeylHiggsWaves.oddProbe => Physics.WeylHiggsWaves.oddProbe,
  GUT.WeylHiggsWaves.oddProbe.eq_1 => Physics.WeylHiggsWaves.oddProbe.eq_1,
  GUT.WeylHiggsWaves.odd_derivative_zero => Physics.WeylHiggsWaves.odd_derivative_zero,
  GUT.WeylHiggsWaves.odd_pair => Physics.WeylHiggsWaves.odd_pair,
  GUT.WeylHiggsWaves.probe => Physics.WeylHiggsWaves.probe
]

assert_compatible GUT.WeylHiggsWaves.Odd0 => Physics.WeylHiggsWaves.Odd0
assert_compatible GUT.WeylHiggsWaves.annihilates => Physics.WeylHiggsWaves.annihilates
assert_compatible GUT.WeylHiggsWaves.augmentation => Physics.WeylHiggsWaves.augmentation
assert_compatible GUT.WeylHiggsWaves.augmentation.eq_1 => Physics.WeylHiggsWaves.augmentation.eq_1
assert_compatible GUT.WeylHiggsWaves.component_zero => Physics.WeylHiggsWaves.component_zero
assert_compatible GUT.WeylHiggsWaves.conserving => Physics.WeylHiggsWaves.conserving
assert_compatible GUT.WeylHiggsWaves.evaluation => Physics.WeylHiggsWaves.evaluation
assert_compatible GUT.WeylHiggsWaves.momenta => Physics.WeylHiggsWaves.momenta
assert_compatible GUT.WeylHiggsWaves.momenta.eq_1 => Physics.WeylHiggsWaves.momenta.eq_1
assert_compatible GUT.WeylHiggsWaves.null => Physics.WeylHiggsWaves.null
assert_compatible GUT.WeylHiggsWaves.oddProbe => Physics.WeylHiggsWaves.oddProbe
assert_compatible GUT.WeylHiggsWaves.oddProbe.eq_1 => Physics.WeylHiggsWaves.oddProbe.eq_1
assert_compatible GUT.WeylHiggsWaves.odd_derivative_zero => Physics.WeylHiggsWaves.odd_derivative_zero
assert_compatible GUT.WeylHiggsWaves.odd_pair => Physics.WeylHiggsWaves.odd_pair
assert_compatible GUT.WeylHiggsWaves.probe => Physics.WeylHiggsWaves.probe
