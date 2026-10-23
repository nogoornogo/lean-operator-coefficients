import Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalUpper
import Physics.FieldTheory.Jets.HiggsQuarticFourInternalControls
import Math.LinearAlgebra.SevenScalarConstraints
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Higgs.QuarticFour.HiggsQuarticFourInternalUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsQuarticFourInternalControls.field.eq_1 => Physics.HiggsQuarticFourInternalControls.field.eq_1,
  GUT.HiggsQuarticFourInternalUpper.K => Physics.HiggsQuarticFourInternalUpper.K,
  GUT.HiggsQuarticFourInternalUpper.K.eq_1 => Physics.HiggsQuarticFourInternalUpper.K.eq_1,
  GUT.HiggsQuarticFourInternalUpper.K_grade => Physics.HiggsQuarticFourInternalUpper.K_grade,
  GUT.HiggsQuarticFourInternalUpper.K_left => Physics.HiggsQuarticFourInternalUpper.K_left,
  GUT.HiggsQuarticFourInternalUpper.K_right => Physics.HiggsQuarticFourInternalUpper.K_right,
  GUT.HiggsQuarticFourInternalUpper.K_swap => Physics.HiggsQuarticFourInternalUpper.K_swap,
  GUT.HiggsQuarticFourInternalUpper.eigen_nontrivial => Physics.HiggsQuarticFourInternalUpper.eigen_nontrivial,
  GUT.HiggsQuarticFourInternalUpper.field_pairs => Physics.HiggsQuarticFourInternalUpper.field_pairs,
  GUT.HiggsQuarticFourInternalUpper.numerator_nontrivial => Physics.HiggsQuarticFourInternalUpper.numerator_nontrivial,
  GUT.HiggsQuarticFourInternalUpper.pair_add_left => Physics.HiggsQuarticFourInternalUpper.pair_add_left,
  GUT.HiggsQuarticFourInternalUpper.pair_add_right => Physics.HiggsQuarticFourInternalUpper.pair_add_right,
  GUT.HiggsQuarticFourInternalUpper.pair_comm => Physics.HiggsQuarticFourInternalUpper.pair_comm,
  GUT.HiggsQuarticFourInternalUpper.pair_smul_left => Physics.HiggsQuarticFourInternalUpper.pair_smul_left,
  GUT.HiggsQuarticFourInternalUpper.pair_smul_right => Physics.HiggsQuarticFourInternalUpper.pair_smul_right,
  GUT.HiggsQuarticFourInternalUpper.pair_sub_left => Physics.HiggsQuarticFourInternalUpper.pair_sub_left,
  GUT.HiggsQuarticFourInternalUpper.pair_sub_right => Physics.HiggsQuarticFourInternalUpper.pair_sub_right,
  GUT.HiggsQuarticFourInternalUpper.pair_transport => Physics.HiggsQuarticFourInternalUpper.pair_transport,
  GUT.HiggsQuarticFourInternalUpper.q1_K => Physics.HiggsQuarticFourInternalUpper.q1_K,
  GUT.HiggsQuarticFourInternalUpper.q2_K => Physics.HiggsQuarticFourInternalUpper.q2_K,
  GUT.HiggsQuarticFourInternalUpper.q3_K => Physics.HiggsQuarticFourInternalUpper.q3_K,
  GUT.HiggsQuarticFourInternalUpper.rotateField => Physics.HiggsQuarticFourInternalUpper.rotateField,
  GUT.HiggsQuarticFourInternalUpper.rotateField.eq_1 => Physics.HiggsQuarticFourInternalUpper.rotateField.eq_1,
  GUT.HiggsQuarticFourInternalUpper.rotation_field4 => Physics.HiggsQuarticFourInternalUpper.rotation_field4,
  GUT.HiggsQuarticFourInternalUpper.rotation_row0 => Physics.HiggsQuarticFourInternalUpper.rotation_row0,
  GUT.HiggsQuarticFourInternalUpper.rotation_row1 => Physics.HiggsQuarticFourInternalUpper.rotation_row1,
  GUT.HiggsQuarticFourInternalUpper.rotation_row2 => Physics.HiggsQuarticFourInternalUpper.rotation_row2,
  GUT.HiggsQuarticFourInternalUpper.rotation_row3 => Physics.HiggsQuarticFourInternalUpper.rotation_row3,
  GUT.HiggsQuarticFourInternalUpper.seven => Physics.HiggsQuarticFourInternalUpper.seven,
  GUT.HiggsQuarticFourInternalUpper.seven_zero => Physics.HiggsQuarticFourInternalUpper.seven_zero,
  GUT.HiggsQuarticFourInternalUpper.vanish => Physics.HiggsQuarticFourInternalUpper.vanish
]

assert_compatible GUT.HiggsQuarticFourInternalControls.field.eq_1 => Physics.HiggsQuarticFourInternalControls.field.eq_1
assert_compatible GUT.HiggsQuarticFourInternalUpper.K => Physics.HiggsQuarticFourInternalUpper.K
assert_compatible GUT.HiggsQuarticFourInternalUpper.K.eq_1 => Physics.HiggsQuarticFourInternalUpper.K.eq_1
assert_compatible GUT.HiggsQuarticFourInternalUpper.K_grade => Physics.HiggsQuarticFourInternalUpper.K_grade
assert_compatible GUT.HiggsQuarticFourInternalUpper.K_left => Physics.HiggsQuarticFourInternalUpper.K_left
assert_compatible GUT.HiggsQuarticFourInternalUpper.K_right => Physics.HiggsQuarticFourInternalUpper.K_right
assert_compatible GUT.HiggsQuarticFourInternalUpper.K_swap => Physics.HiggsQuarticFourInternalUpper.K_swap
assert_compatible GUT.HiggsQuarticFourInternalUpper.eigen_nontrivial => Physics.HiggsQuarticFourInternalUpper.eigen_nontrivial
assert_compatible GUT.HiggsQuarticFourInternalUpper.field_pairs => Physics.HiggsQuarticFourInternalUpper.field_pairs
assert_compatible GUT.HiggsQuarticFourInternalUpper.numerator_nontrivial => Physics.HiggsQuarticFourInternalUpper.numerator_nontrivial
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_add_left => Physics.HiggsQuarticFourInternalUpper.pair_add_left
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_add_right => Physics.HiggsQuarticFourInternalUpper.pair_add_right
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_comm => Physics.HiggsQuarticFourInternalUpper.pair_comm
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_smul_left => Physics.HiggsQuarticFourInternalUpper.pair_smul_left
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_smul_right => Physics.HiggsQuarticFourInternalUpper.pair_smul_right
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_sub_left => Physics.HiggsQuarticFourInternalUpper.pair_sub_left
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_sub_right => Physics.HiggsQuarticFourInternalUpper.pair_sub_right
assert_compatible GUT.HiggsQuarticFourInternalUpper.pair_transport => Physics.HiggsQuarticFourInternalUpper.pair_transport
assert_compatible GUT.HiggsQuarticFourInternalUpper.q1_K => Physics.HiggsQuarticFourInternalUpper.q1_K
assert_compatible GUT.HiggsQuarticFourInternalUpper.q2_K => Physics.HiggsQuarticFourInternalUpper.q2_K
assert_compatible GUT.HiggsQuarticFourInternalUpper.q3_K => Physics.HiggsQuarticFourInternalUpper.q3_K
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotateField => Physics.HiggsQuarticFourInternalUpper.rotateField
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotateField.eq_1 => Physics.HiggsQuarticFourInternalUpper.rotateField.eq_1
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotation_field4 => Physics.HiggsQuarticFourInternalUpper.rotation_field4
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotation_row0 => Physics.HiggsQuarticFourInternalUpper.rotation_row0
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotation_row1 => Physics.HiggsQuarticFourInternalUpper.rotation_row1
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotation_row2 => Physics.HiggsQuarticFourInternalUpper.rotation_row2
assert_compatible GUT.HiggsQuarticFourInternalUpper.rotation_row3 => Physics.HiggsQuarticFourInternalUpper.rotation_row3
assert_compatible GUT.HiggsQuarticFourInternalUpper.seven => Physics.HiggsQuarticFourInternalUpper.seven
assert_compatible GUT.HiggsQuarticFourInternalUpper.seven_zero => Physics.HiggsQuarticFourInternalUpper.seven_zero
assert_compatible GUT.HiggsQuarticFourInternalUpper.vanish => Physics.HiggsQuarticFourInternalUpper.vanish
