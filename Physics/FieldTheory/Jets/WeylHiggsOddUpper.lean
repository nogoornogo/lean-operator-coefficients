import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsOddUpper
import Physics.FieldTheory.Jets.WeylHiggsLorentzUpper
import Physics.FieldTheory.Jets.WeylHiggsFirstSource
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsOddUpper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsLorentzUpper.component_swap_second => Physics.WeylHiggsLorentzUpper.component_swap_second,
  GUT.WeylHiggsLorentzUpper.instAddCommGroupA_physics_1 => Physics.WeylHiggsLorentzUpper.instAddCommGroupA_physics_1,
  GUT.WeylHiggsLorentzUpper.instModuleComplexA_physics_1 => Physics.WeylHiggsLorentzUpper.instModuleComplexA_physics_1,
  GUT.WeylHiggsLorentzUpper.instRingA_physics_1 => Physics.WeylHiggsLorentzUpper.instRingA_physics_1,
  GUT.WeylHiggsLorentzUpper.odd_first_swap => Physics.WeylHiggsLorentzUpper.odd_first_swap,
  GUT.WeylHiggsLorentzUpper.second_zero => Physics.WeylHiggsLorentzUpper.second_zero
]

assert_compatible GUT.WeylHiggsLorentzUpper.component_swap_second => Physics.WeylHiggsLorentzUpper.component_swap_second
assert_compatible GUT.WeylHiggsLorentzUpper.instAddCommGroupA_physics_1 => Physics.WeylHiggsLorentzUpper.instAddCommGroupA_physics_1
assert_compatible GUT.WeylHiggsLorentzUpper.instModuleComplexA_physics_1 => Physics.WeylHiggsLorentzUpper.instModuleComplexA_physics_1
assert_compatible GUT.WeylHiggsLorentzUpper.instRingA_physics_1 => Physics.WeylHiggsLorentzUpper.instRingA_physics_1
assert_compatible GUT.WeylHiggsLorentzUpper.odd_first_swap => Physics.WeylHiggsLorentzUpper.odd_first_swap
assert_compatible GUT.WeylHiggsLorentzUpper.second_zero => Physics.WeylHiggsLorentzUpper.second_zero
