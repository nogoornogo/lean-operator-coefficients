import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLorentzUpper
import Physics.FieldTheory.Jets.HiggsQuarticFourReduction
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourLorentzUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourLorentzUpper.A => Physics.HiggsQuarticFourLorentzUpper.A,
  GUT.HiggsQuarticFourLorentzUpper.D => Physics.HiggsQuarticFourLorentzUpper.D,
  GUT.HiggsQuarticFourLorentzUpper.J => Physics.HiggsQuarticFourLorentzUpper.J,
  GUT.HiggsQuarticFourLorentzUpper.W => Physics.HiggsQuarticFourLorentzUpper.W,
  GUT.HiggsQuarticFourLorentzUpper.W.eq_1 => Physics.HiggsQuarticFourLorentzUpper.W.eq_1,
  GUT.HiggsQuarticFourLorentzUpper.dirD_mem => Physics.HiggsQuarticFourLorentzUpper.dirD_mem,
  GUT.HiggsQuarticFourLorentzUpper.double_commute => Physics.HiggsQuarticFourLorentzUpper.double_commute,
  GUT.HiggsQuarticFourLorentzUpper.eta => Physics.HiggsQuarticFourLorentzUpper.eta,
  GUT.HiggsQuarticFourLorentzUpper.first_ibp => Physics.HiggsQuarticFourLorentzUpper.first_ibp,
  GUT.HiggsQuarticFourLorentzUpper.lower_word_zero => Physics.HiggsQuarticFourLorentzUpper.lower_word_zero,
  GUT.HiggsQuarticFourLorentzUpper.trace_j2 => Physics.HiggsQuarticFourLorentzUpper.trace_j2,
  GUT.HiggsQuarticFourLorentzUpper.trace_j3 => Physics.HiggsQuarticFourLorentzUpper.trace_j3,
  GUT.HiggsQuarticFourLorentzUpper.trace_j4 => Physics.HiggsQuarticFourLorentzUpper.trace_j4,
  GUT.HiggsQuarticFourLorentzUpper.trace_word_mem => Physics.HiggsQuarticFourLorentzUpper.trace_word_mem,
  GUT.HiggsQuarticFourLorentzUpper.trace_zero => Physics.HiggsQuarticFourLorentzUpper.trace_zero,
  GUT.HiggsQuarticFourLorentzUpper.whole_grade_zero => Physics.HiggsQuarticFourLorentzUpper.whole_grade_zero,
  GUT.HiggsQuarticFourLorentzUpper.word_zero => Physics.HiggsQuarticFourLorentzUpper.word_zero
]

assert_compatible GUT.HiggsQuarticFourLorentzUpper.A => Physics.HiggsQuarticFourLorentzUpper.A
assert_compatible GUT.HiggsQuarticFourLorentzUpper.D => Physics.HiggsQuarticFourLorentzUpper.D
assert_compatible GUT.HiggsQuarticFourLorentzUpper.J => Physics.HiggsQuarticFourLorentzUpper.J
assert_compatible GUT.HiggsQuarticFourLorentzUpper.W => Physics.HiggsQuarticFourLorentzUpper.W
assert_compatible GUT.HiggsQuarticFourLorentzUpper.W.eq_1 => Physics.HiggsQuarticFourLorentzUpper.W.eq_1
assert_compatible GUT.HiggsQuarticFourLorentzUpper.dirD_mem => Physics.HiggsQuarticFourLorentzUpper.dirD_mem
assert_compatible GUT.HiggsQuarticFourLorentzUpper.double_commute => Physics.HiggsQuarticFourLorentzUpper.double_commute
assert_compatible GUT.HiggsQuarticFourLorentzUpper.eta => Physics.HiggsQuarticFourLorentzUpper.eta
assert_compatible GUT.HiggsQuarticFourLorentzUpper.first_ibp => Physics.HiggsQuarticFourLorentzUpper.first_ibp
assert_compatible GUT.HiggsQuarticFourLorentzUpper.lower_word_zero => Physics.HiggsQuarticFourLorentzUpper.lower_word_zero
assert_compatible GUT.HiggsQuarticFourLorentzUpper.trace_j2 => Physics.HiggsQuarticFourLorentzUpper.trace_j2
assert_compatible GUT.HiggsQuarticFourLorentzUpper.trace_j3 => Physics.HiggsQuarticFourLorentzUpper.trace_j3
assert_compatible GUT.HiggsQuarticFourLorentzUpper.trace_j4 => Physics.HiggsQuarticFourLorentzUpper.trace_j4
assert_compatible GUT.HiggsQuarticFourLorentzUpper.trace_word_mem => Physics.HiggsQuarticFourLorentzUpper.trace_word_mem
assert_compatible GUT.HiggsQuarticFourLorentzUpper.trace_zero => Physics.HiggsQuarticFourLorentzUpper.trace_zero
assert_compatible GUT.HiggsQuarticFourLorentzUpper.whole_grade_zero => Physics.HiggsQuarticFourLorentzUpper.whole_grade_zero
assert_compatible GUT.HiggsQuarticFourLorentzUpper.word_zero => Physics.HiggsQuarticFourLorentzUpper.word_zero
