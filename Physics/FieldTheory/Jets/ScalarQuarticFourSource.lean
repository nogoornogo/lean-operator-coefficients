import Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourSource
import Physics.FieldTheory.Jets.ScalarQuarticFourTensors
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.QuarticFour.ScalarQuarticFourSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarQuarticFourSource.J => Physics.ScalarQuarticFourSource.J,
  GUT.ScalarQuarticFourSource.grade_eq_span => Physics.ScalarQuarticFourSource.grade_eq_span,
  GUT.ScalarQuarticFourSource.jet0 => Physics.ScalarQuarticFourSource.jet0,
  GUT.ScalarQuarticFourSource.jet1 => Physics.ScalarQuarticFourSource.jet1,
  GUT.ScalarQuarticFourSource.jet2 => Physics.ScalarQuarticFourSource.jet2,
  GUT.ScalarQuarticFourSource.jet3 => Physics.ScalarQuarticFourSource.jet3,
  GUT.ScalarQuarticFourSource.jet4 => Physics.ScalarQuarticFourSource.jet4,
  GUT.ScalarQuarticFourSource.partitions => Physics.ScalarQuarticFourSource.partitions,
  GUT.ScalarQuarticFourSource.product_mem => Physics.ScalarQuarticFourSource.product_mem,
  GUT.ScalarQuarticFourSource.wordSpan => Physics.ScalarQuarticFourSource.wordSpan,
  GUT.ScalarQuarticFourSource.word_mem => Physics.ScalarQuarticFourSource.word_mem,
  GUT.ScalarQuarticFourSource.words => Physics.ScalarQuarticFourSource.words
]

assert_compatible GUT.ScalarQuarticFourSource.J => Physics.ScalarQuarticFourSource.J
assert_compatible GUT.ScalarQuarticFourSource.grade_eq_span => Physics.ScalarQuarticFourSource.grade_eq_span
assert_compatible GUT.ScalarQuarticFourSource.jet0 => Physics.ScalarQuarticFourSource.jet0
assert_compatible GUT.ScalarQuarticFourSource.jet1 => Physics.ScalarQuarticFourSource.jet1
assert_compatible GUT.ScalarQuarticFourSource.jet2 => Physics.ScalarQuarticFourSource.jet2
assert_compatible GUT.ScalarQuarticFourSource.jet3 => Physics.ScalarQuarticFourSource.jet3
assert_compatible GUT.ScalarQuarticFourSource.jet4 => Physics.ScalarQuarticFourSource.jet4
assert_compatible GUT.ScalarQuarticFourSource.partitions => Physics.ScalarQuarticFourSource.partitions
assert_compatible GUT.ScalarQuarticFourSource.product_mem => Physics.ScalarQuarticFourSource.product_mem
assert_compatible GUT.ScalarQuarticFourSource.wordSpan => Physics.ScalarQuarticFourSource.wordSpan
assert_compatible GUT.ScalarQuarticFourSource.word_mem => Physics.ScalarQuarticFourSource.word_mem
assert_compatible GUT.ScalarQuarticFourSource.words => Physics.ScalarQuarticFourSource.words
