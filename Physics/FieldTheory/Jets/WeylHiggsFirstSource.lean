import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstSource
import Physics.FieldTheory.Jets.WeylHiggsFirstTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsFirstSource instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsFirstSource.first_even => Physics.WeylHiggsFirstSource.first_even,
  GUT.WeylHiggsFirstSource.first_odd => Physics.WeylHiggsFirstSource.first_odd,
  GUT.WeylHiggsFirstSource.grade_le_span => Physics.WeylHiggsFirstSource.grade_le_span,
  GUT.WeylHiggsFirstSource.instAddCommGroupA_physics => Physics.WeylHiggsFirstSource.instAddCommGroupA_physics,
  GUT.WeylHiggsFirstSource.instModuleComplexA_physics => Physics.WeylHiggsFirstSource.instModuleComplexA_physics,
  GUT.WeylHiggsFirstSource.instRingA_physics => Physics.WeylHiggsFirstSource.instRingA_physics,
  GUT.WeylHiggsFirstSource.markOrder => Physics.WeylHiggsFirstSource.markOrder,
  GUT.WeylHiggsFirstSource.markOrder.eq_1 => Physics.WeylHiggsFirstSource.markOrder.eq_1,
  GUT.WeylHiggsFirstSource.words => Physics.WeylHiggsFirstSource.words,
  GUT.WeylHiggsFirstSource.zero_of_words => Physics.WeylHiggsFirstSource.zero_of_words,
  GUT.WeylHiggsFirstTensor.evenField.eq_1 => Physics.WeylHiggsFirstTensor.evenField.eq_1,
  GUT.WeylHiggsFirstTensor.word.eq_1 => Physics.WeylHiggsFirstTensor.word.eq_1
]

assert_compatible GUT.WeylHiggsFirstSource.first_even => Physics.WeylHiggsFirstSource.first_even
assert_compatible GUT.WeylHiggsFirstSource.first_odd => Physics.WeylHiggsFirstSource.first_odd
assert_compatible GUT.WeylHiggsFirstSource.grade_le_span => Physics.WeylHiggsFirstSource.grade_le_span
assert_compatible GUT.WeylHiggsFirstSource.instAddCommGroupA_physics => Physics.WeylHiggsFirstSource.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsFirstSource.instModuleComplexA_physics => Physics.WeylHiggsFirstSource.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsFirstSource.instRingA_physics => Physics.WeylHiggsFirstSource.instRingA_physics
assert_compatible GUT.WeylHiggsFirstSource.markOrder => Physics.WeylHiggsFirstSource.markOrder
assert_compatible GUT.WeylHiggsFirstSource.markOrder.eq_1 => Physics.WeylHiggsFirstSource.markOrder.eq_1
assert_compatible GUT.WeylHiggsFirstSource.words => Physics.WeylHiggsFirstSource.words
assert_compatible GUT.WeylHiggsFirstSource.zero_of_words => Physics.WeylHiggsFirstSource.zero_of_words
assert_compatible GUT.WeylHiggsFirstTensor.evenField.eq_1 => Physics.WeylHiggsFirstTensor.evenField.eq_1
assert_compatible GUT.WeylHiggsFirstTensor.word.eq_1 => Physics.WeylHiggsFirstTensor.word.eq_1
