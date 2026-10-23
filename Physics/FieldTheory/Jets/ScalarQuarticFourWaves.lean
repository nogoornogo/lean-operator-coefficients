import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWaves
import Physics.FieldTheory.Jets.ScalarQuarticFourTensors
import Math.Algebra.FourWavePolarization
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourWaves instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticFourWaves.annihilates => Physics.ScalarQuarticFourWaves.annihilates,
  GUT.ScalarQuarticFourWaves.d_linear => Physics.ScalarQuarticFourWaves.d_linear,
  GUT.ScalarQuarticFourWaves.evaluation_field => Physics.ScalarQuarticFourWaves.evaluation_field,
  GUT.ScalarQuarticFourWaves.evaluation_j1 => Physics.ScalarQuarticFourWaves.evaluation_j1,
  GUT.ScalarQuarticFourWaves.evaluation_j2 => Physics.ScalarQuarticFourWaves.evaluation_j2,
  GUT.ScalarQuarticFourWaves.evaluation_j3 => Physics.ScalarQuarticFourWaves.evaluation_j3,
  GUT.ScalarQuarticFourWaves.evaluation_j4 => Physics.ScalarQuarticFourWaves.evaluation_j4,
  GUT.ScalarQuarticFourWaves.evaluation_wave => Physics.ScalarQuarticFourWaves.evaluation_wave,
  GUT.ScalarQuarticFourWaves.ideal_zero => Physics.ScalarQuarticFourWaves.ideal_zero,
  GUT.ScalarQuarticFourWaves.word_value => Physics.ScalarQuarticFourWaves.word_value
]

assert_compatible GUT.ScalarQuarticFourWaves.annihilates => Physics.ScalarQuarticFourWaves.annihilates
assert_compatible GUT.ScalarQuarticFourWaves.d_linear => Physics.ScalarQuarticFourWaves.d_linear
assert_compatible GUT.ScalarQuarticFourWaves.evaluation_field => Physics.ScalarQuarticFourWaves.evaluation_field
assert_compatible GUT.ScalarQuarticFourWaves.evaluation_j1 => Physics.ScalarQuarticFourWaves.evaluation_j1
assert_compatible GUT.ScalarQuarticFourWaves.evaluation_j2 => Physics.ScalarQuarticFourWaves.evaluation_j2
assert_compatible GUT.ScalarQuarticFourWaves.evaluation_j3 => Physics.ScalarQuarticFourWaves.evaluation_j3
assert_compatible GUT.ScalarQuarticFourWaves.evaluation_j4 => Physics.ScalarQuarticFourWaves.evaluation_j4
assert_compatible GUT.ScalarQuarticFourWaves.evaluation_wave => Physics.ScalarQuarticFourWaves.evaluation_wave
assert_compatible GUT.ScalarQuarticFourWaves.ideal_zero => Physics.ScalarQuarticFourWaves.ideal_zero
assert_compatible GUT.ScalarQuarticFourWaves.word_value => Physics.ScalarQuarticFourWaves.word_value
