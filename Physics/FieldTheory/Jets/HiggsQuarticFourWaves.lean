import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourWaves
import Physics.FieldTheory.Jets.HiggsQuarticFourInput
import Math.Algebra.ColoredFourWaveEvaluation
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourWaves instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourWaves.annihilates => Physics.HiggsQuarticFourWaves.annihilates,
  GUT.HiggsQuarticFourWaves.ev => Physics.HiggsQuarticFourWaves.ev,
  GUT.HiggsQuarticFourWaves.ideal_zero => Physics.HiggsQuarticFourWaves.ideal_zero,
  GUT.HiggsQuarticFourWaves.onJets => Physics.HiggsQuarticFourWaves.onJets,
  GUT.HiggsQuarticFourWaves.relations_eq => Physics.HiggsQuarticFourWaves.relations_eq,
  GUT.HiggsQuarticFourWaves.seed_zero => Physics.HiggsQuarticFourWaves.seed_zero
]

assert_compatible GUT.HiggsQuarticFourWaves.annihilates => Physics.HiggsQuarticFourWaves.annihilates
assert_compatible GUT.HiggsQuarticFourWaves.ev => Physics.HiggsQuarticFourWaves.ev
assert_compatible GUT.HiggsQuarticFourWaves.ideal_zero => Physics.HiggsQuarticFourWaves.ideal_zero
assert_compatible GUT.HiggsQuarticFourWaves.onJets => Physics.HiggsQuarticFourWaves.onJets
assert_compatible GUT.HiggsQuarticFourWaves.relations_eq => Physics.HiggsQuarticFourWaves.relations_eq
assert_compatible GUT.HiggsQuarticFourWaves.seed_zero => Physics.HiggsQuarticFourWaves.seed_zero
