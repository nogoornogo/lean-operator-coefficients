import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsLorentzUpper
import Physics.FieldTheory.Jets.WeylHiggsFirstTensor
import Physics.FieldTheory.Jets.WeylDirectionInvariant.LL
import Physics.FieldTheory.Jets.WeylDirectionInvariant.LR
import Physics.FieldTheory.Jets.WeylDirectionInvariant.RL
import Physics.FieldTheory.Jets.WeylDirectionInvariant.RR
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsLorentzUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsLorentzUpper.C => Physics.WeylHiggsLorentzUpper.C,
  GUT.WeylHiggsLorentzUpper.component_formula => Physics.WeylHiggsLorentzUpper.component_formula,
  GUT.WeylHiggsLorentzUpper.component_word => Physics.WeylHiggsLorentzUpper.component_word,
  GUT.WeylHiggsLorentzUpper.first_zero => Physics.WeylHiggsLorentzUpper.first_zero,
  GUT.WeylHiggsLorentzUpper.instAddCommGroupA_physics => Physics.WeylHiggsLorentzUpper.instAddCommGroupA_physics,
  GUT.WeylHiggsLorentzUpper.instModuleComplexA_physics => Physics.WeylHiggsLorentzUpper.instModuleComplexA_physics,
  GUT.WeylHiggsLorentzUpper.instRingA_physics => Physics.WeylHiggsLorentzUpper.instRingA_physics,
  GUT.WeylHiggsLorentzUpper.left_first_coordinate_zero => Physics.WeylHiggsLorentzUpper.left_first_coordinate_zero,
  GUT.WeylHiggsLorentzUpper.right_first_coordinate_zero => Physics.WeylHiggsLorentzUpper.right_first_coordinate_zero,
  GUT.WeylHiggsLorentzUpper.seed_first_value => Physics.WeylHiggsLorentzUpper.seed_first_value,
  GUT.WeylHiggsLorentzUpper.seed_first_zero => Physics.WeylHiggsLorentzUpper.seed_first_zero,
  GUT.WeylHiggsLorentzUpper.seed_mem => Physics.WeylHiggsLorentzUpper.seed_mem
]

assert_compatible GUT.WeylHiggsLorentzUpper.C => Physics.WeylHiggsLorentzUpper.C
assert_compatible GUT.WeylHiggsLorentzUpper.component_formula => Physics.WeylHiggsLorentzUpper.component_formula
assert_compatible GUT.WeylHiggsLorentzUpper.component_word => Physics.WeylHiggsLorentzUpper.component_word
assert_compatible GUT.WeylHiggsLorentzUpper.first_zero => Physics.WeylHiggsLorentzUpper.first_zero
assert_compatible GUT.WeylHiggsLorentzUpper.instAddCommGroupA_physics => Physics.WeylHiggsLorentzUpper.instAddCommGroupA_physics
assert_compatible GUT.WeylHiggsLorentzUpper.instModuleComplexA_physics => Physics.WeylHiggsLorentzUpper.instModuleComplexA_physics
assert_compatible GUT.WeylHiggsLorentzUpper.instRingA_physics => Physics.WeylHiggsLorentzUpper.instRingA_physics
assert_compatible GUT.WeylHiggsLorentzUpper.left_first_coordinate_zero => Physics.WeylHiggsLorentzUpper.left_first_coordinate_zero
assert_compatible GUT.WeylHiggsLorentzUpper.right_first_coordinate_zero => Physics.WeylHiggsLorentzUpper.right_first_coordinate_zero
assert_compatible GUT.WeylHiggsLorentzUpper.seed_first_value => Physics.WeylHiggsLorentzUpper.seed_first_value
assert_compatible GUT.WeylHiggsLorentzUpper.seed_first_zero => Physics.WeylHiggsLorentzUpper.seed_first_zero
assert_compatible GUT.WeylHiggsLorentzUpper.seed_mem => Physics.WeylHiggsLorentzUpper.seed_mem
