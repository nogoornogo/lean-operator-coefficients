import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourReduction
import Physics.FieldTheory.Jets.HiggsQuarticFourTensors
import Physics.FieldTheory.Jets.HiggsQuarticFourWaves
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourReduction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourReduction.B2 => Physics.HiggsQuarticFourReduction.B2,
  GUT.HiggsQuarticFourReduction.B2.eq_1 => Physics.HiggsQuarticFourReduction.B2.eq_1,
  GUT.HiggsQuarticFourReduction.B2_zero => Physics.HiggsQuarticFourReduction.B2_zero,
  GUT.HiggsQuarticFourReduction.C3 => Physics.HiggsQuarticFourReduction.C3,
  GUT.HiggsQuarticFourReduction.C3.eq_1 => Physics.HiggsQuarticFourReduction.C3.eq_1,
  GUT.HiggsQuarticFourReduction.C3_relation => Physics.HiggsQuarticFourReduction.C3_relation,
  GUT.HiggsQuarticFourReduction.C3_swap => Physics.HiggsQuarticFourReduction.C3_swap,
  GUT.HiggsQuarticFourReduction.C3_zero => Physics.HiggsQuarticFourReduction.C3_zero,
  GUT.HiggsQuarticFourReduction.current2 => Physics.HiggsQuarticFourReduction.current2,
  GUT.HiggsQuarticFourReduction.current2.eq_1 => Physics.HiggsQuarticFourReduction.current2.eq_1,
  GUT.HiggsQuarticFourReduction.current3 => Physics.HiggsQuarticFourReduction.current3,
  GUT.HiggsQuarticFourReduction.current3.eq_1 => Physics.HiggsQuarticFourReduction.current3.eq_1,
  GUT.HiggsQuarticFourReduction.derivative_zero => Physics.HiggsQuarticFourReduction.derivative_zero,
  GUT.HiggsQuarticFourReduction.divergence2 => Physics.HiggsQuarticFourReduction.divergence2,
  GUT.HiggsQuarticFourReduction.divergence3 => Physics.HiggsQuarticFourReduction.divergence3,
  GUT.HiggsQuarticFourReduction.eta => Physics.HiggsQuarticFourReduction.eta,
  GUT.HiggsQuarticFourReduction.ideal_zero => Physics.HiggsQuarticFourReduction.ideal_zero,
  GUT.HiggsQuarticFourReduction.wave_mem => Physics.HiggsQuarticFourReduction.wave_mem
]

assert_compatible GUT.HiggsQuarticFourReduction.B2 => Physics.HiggsQuarticFourReduction.B2
assert_compatible GUT.HiggsQuarticFourReduction.B2.eq_1 => Physics.HiggsQuarticFourReduction.B2.eq_1
assert_compatible GUT.HiggsQuarticFourReduction.B2_zero => Physics.HiggsQuarticFourReduction.B2_zero
assert_compatible GUT.HiggsQuarticFourReduction.C3 => Physics.HiggsQuarticFourReduction.C3
assert_compatible GUT.HiggsQuarticFourReduction.C3.eq_1 => Physics.HiggsQuarticFourReduction.C3.eq_1
assert_compatible GUT.HiggsQuarticFourReduction.C3_relation => Physics.HiggsQuarticFourReduction.C3_relation
assert_compatible GUT.HiggsQuarticFourReduction.C3_swap => Physics.HiggsQuarticFourReduction.C3_swap
assert_compatible GUT.HiggsQuarticFourReduction.C3_zero => Physics.HiggsQuarticFourReduction.C3_zero
assert_compatible GUT.HiggsQuarticFourReduction.current2 => Physics.HiggsQuarticFourReduction.current2
assert_compatible GUT.HiggsQuarticFourReduction.current2.eq_1 => Physics.HiggsQuarticFourReduction.current2.eq_1
assert_compatible GUT.HiggsQuarticFourReduction.current3 => Physics.HiggsQuarticFourReduction.current3
assert_compatible GUT.HiggsQuarticFourReduction.current3.eq_1 => Physics.HiggsQuarticFourReduction.current3.eq_1
assert_compatible GUT.HiggsQuarticFourReduction.derivative_zero => Physics.HiggsQuarticFourReduction.derivative_zero
assert_compatible GUT.HiggsQuarticFourReduction.divergence2 => Physics.HiggsQuarticFourReduction.divergence2
assert_compatible GUT.HiggsQuarticFourReduction.divergence3 => Physics.HiggsQuarticFourReduction.divergence3
assert_compatible GUT.HiggsQuarticFourReduction.eta => Physics.HiggsQuarticFourReduction.eta
assert_compatible GUT.HiggsQuarticFourReduction.ideal_zero => Physics.HiggsQuarticFourReduction.ideal_zero
assert_compatible GUT.HiggsQuarticFourReduction.wave_mem => Physics.HiggsQuarticFourReduction.wave_mem
