import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourUpper
import Physics.FieldTheory.Jets.ScalarQuarticFourSource
import Physics.FieldTheory.Jets.LorentzRankFour.Contractions
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticFourUpper.A_grade => Physics.ScalarQuarticFourUpper.A_grade,
  GUT.ScalarQuarticFourUpper.A_word => Physics.ScalarQuarticFourUpper.A_word,
  GUT.ScalarQuarticFourUpper.B_grade => Physics.ScalarQuarticFourUpper.B_grade,
  GUT.ScalarQuarticFourUpper.B_word => Physics.ScalarQuarticFourUpper.B_word,
  GUT.ScalarQuarticFourUpper.C_grade => Physics.ScalarQuarticFourUpper.C_grade,
  GUT.ScalarQuarticFourUpper.C_word => Physics.ScalarQuarticFourUpper.C_word,
  GUT.ScalarQuarticFourUpper.double_commute => Physics.ScalarQuarticFourUpper.double_commute,
  GUT.ScalarQuarticFourUpper.evaluate => Physics.ScalarQuarticFourUpper.evaluate,
  GUT.ScalarQuarticFourUpper.evaluate_injective => Physics.ScalarQuarticFourUpper.evaluate_injective,
  GUT.ScalarQuarticFourUpper.extra_sym_four => Physics.ScalarQuarticFourUpper.extra_sym_four,
  GUT.ScalarQuarticFourUpper.extra_sym_one => Physics.ScalarQuarticFourUpper.extra_sym_one,
  GUT.ScalarQuarticFourUpper.extra_sym_zero => Physics.ScalarQuarticFourUpper.extra_sym_zero,
  GUT.ScalarQuarticFourUpper.generator => Physics.ScalarQuarticFourUpper.generator,
  GUT.ScalarQuarticFourUpper.selected_zero => Physics.ScalarQuarticFourUpper.selected_zero,
  GUT.ScalarQuarticFourUpper.trace_j2 => Physics.ScalarQuarticFourUpper.trace_j2,
  GUT.ScalarQuarticFourUpper.trace_j3 => Physics.ScalarQuarticFourUpper.trace_j3,
  GUT.ScalarQuarticFourUpper.trace_j4 => Physics.ScalarQuarticFourUpper.trace_j4,
  GUT.ScalarQuarticFourUpper.trace_word0 => Physics.ScalarQuarticFourUpper.trace_word0,
  GUT.ScalarQuarticFourUpper.trace_word1 => Physics.ScalarQuarticFourUpper.trace_word1,
  GUT.ScalarQuarticFourUpper.trace_word2 => Physics.ScalarQuarticFourUpper.trace_word2,
  GUT.ScalarQuarticFourUpper.trace_word3 => Physics.ScalarQuarticFourUpper.trace_word3,
  GUT.ScalarQuarticFourUpper.trace_word_mem => Physics.ScalarQuarticFourUpper.trace_word_mem,
  GUT.ScalarQuarticFourUpper.trace_zero => Physics.ScalarQuarticFourUpper.trace_zero,
  GUT.ScalarQuarticFourUpper.value_congr => Physics.ScalarQuarticFourUpper.value_congr,
  GUT.ScalarQuarticFourUpper.whole_grade_zero => Physics.ScalarQuarticFourUpper.whole_grade_zero,
  GUT.ScalarQuarticFourUpper.word_zero => Physics.ScalarQuarticFourUpper.word_zero
]

assert_compatible GUT.ScalarQuarticFourUpper.A_grade => Physics.ScalarQuarticFourUpper.A_grade
assert_compatible GUT.ScalarQuarticFourUpper.A_word => Physics.ScalarQuarticFourUpper.A_word
assert_compatible GUT.ScalarQuarticFourUpper.B_grade => Physics.ScalarQuarticFourUpper.B_grade
assert_compatible GUT.ScalarQuarticFourUpper.B_word => Physics.ScalarQuarticFourUpper.B_word
assert_compatible GUT.ScalarQuarticFourUpper.C_grade => Physics.ScalarQuarticFourUpper.C_grade
assert_compatible GUT.ScalarQuarticFourUpper.C_word => Physics.ScalarQuarticFourUpper.C_word
assert_compatible GUT.ScalarQuarticFourUpper.double_commute => Physics.ScalarQuarticFourUpper.double_commute
assert_compatible GUT.ScalarQuarticFourUpper.evaluate => Physics.ScalarQuarticFourUpper.evaluate
assert_compatible GUT.ScalarQuarticFourUpper.evaluate_injective => Physics.ScalarQuarticFourUpper.evaluate_injective
assert_compatible GUT.ScalarQuarticFourUpper.extra_sym_four => Physics.ScalarQuarticFourUpper.extra_sym_four
assert_compatible GUT.ScalarQuarticFourUpper.extra_sym_one => Physics.ScalarQuarticFourUpper.extra_sym_one
assert_compatible GUT.ScalarQuarticFourUpper.extra_sym_zero => Physics.ScalarQuarticFourUpper.extra_sym_zero
assert_compatible GUT.ScalarQuarticFourUpper.generator => Physics.ScalarQuarticFourUpper.generator
assert_compatible GUT.ScalarQuarticFourUpper.selected_zero => Physics.ScalarQuarticFourUpper.selected_zero
assert_compatible GUT.ScalarQuarticFourUpper.trace_j2 => Physics.ScalarQuarticFourUpper.trace_j2
assert_compatible GUT.ScalarQuarticFourUpper.trace_j3 => Physics.ScalarQuarticFourUpper.trace_j3
assert_compatible GUT.ScalarQuarticFourUpper.trace_j4 => Physics.ScalarQuarticFourUpper.trace_j4
assert_compatible GUT.ScalarQuarticFourUpper.trace_word0 => Physics.ScalarQuarticFourUpper.trace_word0
assert_compatible GUT.ScalarQuarticFourUpper.trace_word1 => Physics.ScalarQuarticFourUpper.trace_word1
assert_compatible GUT.ScalarQuarticFourUpper.trace_word2 => Physics.ScalarQuarticFourUpper.trace_word2
assert_compatible GUT.ScalarQuarticFourUpper.trace_word3 => Physics.ScalarQuarticFourUpper.trace_word3
assert_compatible GUT.ScalarQuarticFourUpper.trace_word_mem => Physics.ScalarQuarticFourUpper.trace_word_mem
assert_compatible GUT.ScalarQuarticFourUpper.trace_zero => Physics.ScalarQuarticFourUpper.trace_zero
assert_compatible GUT.ScalarQuarticFourUpper.value_congr => Physics.ScalarQuarticFourUpper.value_congr
assert_compatible GUT.ScalarQuarticFourUpper.whole_grade_zero => Physics.ScalarQuarticFourUpper.whole_grade_zero
assert_compatible GUT.ScalarQuarticFourUpper.word_zero => Physics.ScalarQuarticFourUpper.word_zero
