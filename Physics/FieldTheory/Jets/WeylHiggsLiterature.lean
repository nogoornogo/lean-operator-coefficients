import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsLiterature
import Physics.FieldTheory.Jets.WeylHiggsSelection
import Physics.FieldTheory.Jets.WeylHiggsCommutingControl
import Physics.FieldTheory.Jets.WeylHiggsProbeControl
import Physics.FieldTheory.Spinor.MinkowskiWeylCurrent
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsLiterature instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsLiterature.dhm_block => Physics.WeylHiggsLiterature.dhm_block,
  GUT.WeylHiggsLiterature.dhm_reversal => Physics.WeylHiggsLiterature.dhm_reversal,
  GUT.WeylHiggsLiterature.generated_native_values => Physics.WeylHiggsLiterature.generated_native_values,
  GUT.WeylHiggsLiterature.instAddCommGroupA_physics => Physics.WeylHiggsLiterature.instAddCommGroupA_physics,
  GUT.WeylHiggsLiterature.instModuleComplexA_physics => Physics.WeylHiggsLiterature.instModuleComplexA_physics,
  GUT.WeylHiggsLiterature.instRingA_physics => Physics.WeylHiggsLiterature.instRingA_physics,
  GUT.WeylHiggsLiterature.li => Physics.WeylHiggsLiterature.li,
  GUT.WeylHiggsLiterature.li.eq_1 => Physics.WeylHiggsLiterature.li.eq_1,
  GUT.WeylHiggsLiterature.li_actual_invariant => Physics.WeylHiggsLiterature.li_actual_invariant,
  GUT.WeylHiggsLiterature.li_murphy => Physics.WeylHiggsLiterature.li_murphy,
  GUT.WeylHiggsLiterature.murphy => Physics.WeylHiggsLiterature.murphy,
  GUT.WeylHiggsLiterature.murphy.eq_1 => Physics.WeylHiggsLiterature.murphy.eq_1,
  GUT.WeylHiggsLiterature.murphySelected => Physics.WeylHiggsLiterature.murphySelected,
  GUT.WeylHiggsLiterature.murphy_actual_invariant => Physics.WeylHiggsLiterature.murphy_actual_invariant,
  GUT.WeylHiggsLiterature.raw_value_control => Physics.WeylHiggsLiterature.raw_value_control,
  GUT.WeylHiggsLiterature.selected_native_values => Physics.WeylHiggsLiterature.selected_native_values
]

assert_compatible GUT.WeylHiggsLiterature.dhm_block => Physics.WeylHiggsLiterature.dhm_block
assert_compatible GUT.WeylHiggsLiterature.dhm_reversal => Physics.WeylHiggsLiterature.dhm_reversal
assert_compatible GUT.WeylHiggsLiterature.generated_native_values => Physics.WeylHiggsLiterature.generated_native_values
assert_compatible GUT.WeylHiggsLiterature.instAddCommGroupA_physics => Physics.WeylHiggsLiterature.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsLiterature.instModuleComplexA_physics => Physics.WeylHiggsLiterature.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsLiterature.instRingA_physics => Physics.WeylHiggsLiterature.instRingA_physics
assert_compatible GUT.WeylHiggsLiterature.li => Physics.WeylHiggsLiterature.li
assert_compatible GUT.WeylHiggsLiterature.li.eq_1 => Physics.WeylHiggsLiterature.li.eq_1
assert_compatible GUT.WeylHiggsLiterature.li_actual_invariant => Physics.WeylHiggsLiterature.li_actual_invariant
assert_compatible GUT.WeylHiggsLiterature.li_murphy => Physics.WeylHiggsLiterature.li_murphy
assert_compatible GUT.WeylHiggsLiterature.murphy => Physics.WeylHiggsLiterature.murphy
assert_compatible GUT.WeylHiggsLiterature.murphy.eq_1 => Physics.WeylHiggsLiterature.murphy.eq_1
assert_compatible GUT.WeylHiggsLiterature.murphySelected => Physics.WeylHiggsLiterature.murphySelected
assert_compatible GUT.WeylHiggsLiterature.murphy_actual_invariant => Physics.WeylHiggsLiterature.murphy_actual_invariant
assert_compatible GUT.WeylHiggsLiterature.raw_value_control => Physics.WeylHiggsLiterature.raw_value_control
assert_compatible GUT.WeylHiggsLiterature.selected_native_values => Physics.WeylHiggsLiterature.selected_native_values
