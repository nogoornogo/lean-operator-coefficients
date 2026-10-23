import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInput
import Physics.FieldTheory.Jets.HiggsStandardInput
import Physics.FieldTheory.Jets.LorentzRankFour.Invariant
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInput instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourInput.P => Physics.HiggsQuarticFourInput.P,
  GUT.HiggsQuarticFourInput.V => Physics.HiggsQuarticFourInput.V,
  GUT.HiggsQuarticFourInput.contracted_coefficients => Physics.HiggsQuarticFourInput.contracted_coefficients,
  GUT.HiggsQuarticFourInput.directionCoefficient => Physics.HiggsQuarticFourInput.directionCoefficient,
  GUT.HiggsQuarticFourInput.directionCoefficient.eq_1 => Physics.HiggsQuarticFourInput.directionCoefficient.eq_1,
  GUT.HiggsQuarticFourInput.dot => Physics.HiggsQuarticFourInput.dot,
  GUT.HiggsQuarticFourInput.dot.eq_1 => Physics.HiggsQuarticFourInput.dot.eq_1,
  GUT.HiggsQuarticFourInput.dot_covariant => Physics.HiggsQuarticFourInput.dot_covariant,
  GUT.HiggsQuarticFourInput.evaluate => Physics.HiggsQuarticFourInput.evaluate,
  GUT.HiggsQuarticFourInput.first_X => Physics.HiggsQuarticFourInput.first_X,
  GUT.HiggsQuarticFourInput.first_grade => Physics.HiggsQuarticFourInput.first_grade,
  GUT.HiggsQuarticFourInput.h_grade => Physics.HiggsQuarticFourInput.h_grade,
  GUT.HiggsQuarticFourInput.internal_m => Physics.HiggsQuarticFourInput.internal_m,
  GUT.HiggsQuarticFourInput.internal_q1 => Physics.HiggsQuarticFourInput.internal_q1,
  GUT.HiggsQuarticFourInput.internal_q2 => Physics.HiggsQuarticFourInput.internal_q2,
  GUT.HiggsQuarticFourInput.internal_q3 => Physics.HiggsQuarticFourInput.internal_q3,
  GUT.HiggsQuarticFourInput.invariant_q1 => Physics.HiggsQuarticFourInput.invariant_q1,
  GUT.HiggsQuarticFourInput.invariant_q2 => Physics.HiggsQuarticFourInput.invariant_q2,
  GUT.HiggsQuarticFourInput.invariant_q3 => Physics.HiggsQuarticFourInput.invariant_q3,
  GUT.HiggsQuarticFourInput.lorentz_pair => Physics.HiggsQuarticFourInput.lorentz_pair,
  GUT.HiggsQuarticFourInput.lorentz_q1 => Physics.HiggsQuarticFourInput.lorentz_q1,
  GUT.HiggsQuarticFourInput.lorentz_q2 => Physics.HiggsQuarticFourInput.lorentz_q2,
  GUT.HiggsQuarticFourInput.lorentz_q3 => Physics.HiggsQuarticFourInput.lorentz_q3,
  GUT.HiggsQuarticFourInput.m_canonical => Physics.HiggsQuarticFourInput.m_canonical,
  GUT.HiggsQuarticFourInput.m_grade => Physics.HiggsQuarticFourInput.m_grade,
  GUT.HiggsQuarticFourInput.pair_dot => Physics.HiggsQuarticFourInput.pair_dot,
  GUT.HiggsQuarticFourInput.q1_grade => Physics.HiggsQuarticFourInput.q1_grade,
  GUT.HiggsQuarticFourInput.q1_pairs => Physics.HiggsQuarticFourInput.q1_pairs,
  GUT.HiggsQuarticFourInput.q2_grade => Physics.HiggsQuarticFourInput.q2_grade,
  GUT.HiggsQuarticFourInput.q2_pairs => Physics.HiggsQuarticFourInput.q2_pairs,
  GUT.HiggsQuarticFourInput.q3_grade => Physics.HiggsQuarticFourInput.q3_grade,
  GUT.HiggsQuarticFourInput.q3_pairs => Physics.HiggsQuarticFourInput.q3_pairs,
  GUT.HiggsQuarticFourInput.representatives => Physics.HiggsQuarticFourInput.representatives,
  GUT.HiggsQuarticFourInput.selected => Physics.HiggsQuarticFourInput.selected,
  GUT.HiggsQuarticFourInput.stable => Physics.HiggsQuarticFourInput.stable
]

assert_compatible GUT.HiggsQuarticFourInput.P => Physics.HiggsQuarticFourInput.P
assert_compatible GUT.HiggsQuarticFourInput.V => Physics.HiggsQuarticFourInput.V
assert_compatible GUT.HiggsQuarticFourInput.contracted_coefficients => Physics.HiggsQuarticFourInput.contracted_coefficients
assert_compatible GUT.HiggsQuarticFourInput.directionCoefficient => Physics.HiggsQuarticFourInput.directionCoefficient
assert_compatible GUT.HiggsQuarticFourInput.directionCoefficient.eq_1 => Physics.HiggsQuarticFourInput.directionCoefficient.eq_1
assert_compatible GUT.HiggsQuarticFourInput.dot => Physics.HiggsQuarticFourInput.dot
assert_compatible GUT.HiggsQuarticFourInput.dot.eq_1 => Physics.HiggsQuarticFourInput.dot.eq_1
assert_compatible GUT.HiggsQuarticFourInput.dot_covariant => Physics.HiggsQuarticFourInput.dot_covariant
assert_compatible GUT.HiggsQuarticFourInput.evaluate => Physics.HiggsQuarticFourInput.evaluate
assert_compatible GUT.HiggsQuarticFourInput.first_X => Physics.HiggsQuarticFourInput.first_X
assert_compatible GUT.HiggsQuarticFourInput.first_grade => Physics.HiggsQuarticFourInput.first_grade
assert_compatible GUT.HiggsQuarticFourInput.h_grade => Physics.HiggsQuarticFourInput.h_grade
assert_compatible GUT.HiggsQuarticFourInput.internal_m => Physics.HiggsQuarticFourInput.internal_m
assert_compatible GUT.HiggsQuarticFourInput.internal_q1 => Physics.HiggsQuarticFourInput.internal_q1
assert_compatible GUT.HiggsQuarticFourInput.internal_q2 => Physics.HiggsQuarticFourInput.internal_q2
assert_compatible GUT.HiggsQuarticFourInput.internal_q3 => Physics.HiggsQuarticFourInput.internal_q3
assert_compatible GUT.HiggsQuarticFourInput.invariant_q1 => Physics.HiggsQuarticFourInput.invariant_q1
assert_compatible GUT.HiggsQuarticFourInput.invariant_q2 => Physics.HiggsQuarticFourInput.invariant_q2
assert_compatible GUT.HiggsQuarticFourInput.invariant_q3 => Physics.HiggsQuarticFourInput.invariant_q3
assert_compatible GUT.HiggsQuarticFourInput.lorentz_pair => Physics.HiggsQuarticFourInput.lorentz_pair
assert_compatible GUT.HiggsQuarticFourInput.lorentz_q1 => Physics.HiggsQuarticFourInput.lorentz_q1
assert_compatible GUT.HiggsQuarticFourInput.lorentz_q2 => Physics.HiggsQuarticFourInput.lorentz_q2
assert_compatible GUT.HiggsQuarticFourInput.lorentz_q3 => Physics.HiggsQuarticFourInput.lorentz_q3
assert_compatible GUT.HiggsQuarticFourInput.m_canonical => Physics.HiggsQuarticFourInput.m_canonical
assert_compatible GUT.HiggsQuarticFourInput.m_grade => Physics.HiggsQuarticFourInput.m_grade
assert_compatible GUT.HiggsQuarticFourInput.pair_dot => Physics.HiggsQuarticFourInput.pair_dot
assert_compatible GUT.HiggsQuarticFourInput.q1_grade => Physics.HiggsQuarticFourInput.q1_grade
assert_compatible GUT.HiggsQuarticFourInput.q1_pairs => Physics.HiggsQuarticFourInput.q1_pairs
assert_compatible GUT.HiggsQuarticFourInput.q2_grade => Physics.HiggsQuarticFourInput.q2_grade
assert_compatible GUT.HiggsQuarticFourInput.q2_pairs => Physics.HiggsQuarticFourInput.q2_pairs
assert_compatible GUT.HiggsQuarticFourInput.q3_grade => Physics.HiggsQuarticFourInput.q3_grade
assert_compatible GUT.HiggsQuarticFourInput.q3_pairs => Physics.HiggsQuarticFourInput.q3_pairs
assert_compatible GUT.HiggsQuarticFourInput.representatives => Physics.HiggsQuarticFourInput.representatives
assert_compatible GUT.HiggsQuarticFourInput.selected => Physics.HiggsQuarticFourInput.selected
assert_compatible GUT.HiggsQuarticFourInput.stable => Physics.HiggsQuarticFourInput.stable
