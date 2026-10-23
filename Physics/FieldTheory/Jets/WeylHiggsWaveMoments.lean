import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveMoments
import Physics.FieldTheory.Jets.WeylHiggsWaveWords
import Physics.FieldTheory.Jets.WeylDirectionInvariant.Tensor
import Physics.FieldTheory.Jets.WeylHiggsUpper
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsWaveMoments instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsWaveMoments.even_word_left => Physics.WeylHiggsWaveMoments.even_word_left,
  GUT.WeylHiggsWaveMoments.even_word_right => Physics.WeylHiggsWaveMoments.even_word_right,
  GUT.WeylHiggsWaveMoments.first_word_zero => Physics.WeylHiggsWaveMoments.first_word_zero,
  GUT.WeylHiggsWaveMoments.instAddCommGroupA_physics => Physics.WeylHiggsWaveMoments.instAddCommGroupA_physics,
  GUT.WeylHiggsWaveMoments.instModuleComplexA_physics => Physics.WeylHiggsWaveMoments.instModuleComplexA_physics,
  GUT.WeylHiggsWaveMoments.instRingA_physics => Physics.WeylHiggsWaveMoments.instRingA_physics,
  GUT.WeylHiggsWaveMoments.left_even => Physics.WeylHiggsWaveMoments.left_even,
  GUT.WeylHiggsWaveMoments.marked => Physics.WeylHiggsWaveMoments.marked,
  GUT.WeylHiggsWaveMoments.marked.eq_1 => Physics.WeylHiggsWaveMoments.marked.eq_1,
  GUT.WeylHiggsWaveMoments.marked_color => Physics.WeylHiggsWaveMoments.marked_color,
  GUT.WeylHiggsWaveMoments.reverse_scalar => Physics.WeylHiggsWaveMoments.reverse_scalar,
  GUT.WeylHiggsWaveMoments.right_even => Physics.WeylHiggsWaveMoments.right_even,
  GUT.WeylHiggsWaveMoments.second_word_zero => Physics.WeylHiggsWaveMoments.second_word_zero
]

assert_compatible GUT.WeylHiggsWaveMoments.even_word_left => Physics.WeylHiggsWaveMoments.even_word_left
assert_compatible GUT.WeylHiggsWaveMoments.even_word_right => Physics.WeylHiggsWaveMoments.even_word_right
assert_compatible GUT.WeylHiggsWaveMoments.first_word_zero => Physics.WeylHiggsWaveMoments.first_word_zero
assert_compatible GUT.WeylHiggsWaveMoments.instAddCommGroupA_physics => Physics.WeylHiggsWaveMoments.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsWaveMoments.instModuleComplexA_physics => Physics.WeylHiggsWaveMoments.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsWaveMoments.instRingA_physics => Physics.WeylHiggsWaveMoments.instRingA_physics
assert_compatible GUT.WeylHiggsWaveMoments.left_even => Physics.WeylHiggsWaveMoments.left_even
assert_compatible GUT.WeylHiggsWaveMoments.marked => Physics.WeylHiggsWaveMoments.marked
assert_compatible GUT.WeylHiggsWaveMoments.marked.eq_1 => Physics.WeylHiggsWaveMoments.marked.eq_1
assert_compatible GUT.WeylHiggsWaveMoments.marked_color => Physics.WeylHiggsWaveMoments.marked_color
assert_compatible GUT.WeylHiggsWaveMoments.reverse_scalar => Physics.WeylHiggsWaveMoments.reverse_scalar
assert_compatible GUT.WeylHiggsWaveMoments.right_even => Physics.WeylHiggsWaveMoments.right_even
assert_compatible GUT.WeylHiggsWaveMoments.second_word_zero => Physics.WeylHiggsWaveMoments.second_word_zero
