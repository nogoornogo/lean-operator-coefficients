import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInternalIBP
import Physics.FieldTheory.Jets.WeylHiggsInternalLift
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsInternalIBP instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylHiggsInternalLift.derivative_four => Physics.WeylHiggsInternalLift.derivative_four,
  GUT.WeylHiggsInternalLift.derivative_zero => Physics.WeylHiggsInternalLift.derivative_zero,
  GUT.WeylHiggsInternalLift.first_word_scalar => Physics.WeylHiggsInternalLift.first_word_scalar,
  GUT.WeylHiggsInternalLift.instAddCommGroupA_physics_1 => Physics.WeylHiggsInternalLift.instAddCommGroupA_physics_1,
  GUT.WeylHiggsInternalLift.instModuleComplexA_physics_1 => Physics.WeylHiggsInternalLift.instModuleComplexA_physics_1,
  GUT.WeylHiggsInternalLift.instRingA_physics_1 => Physics.WeylHiggsInternalLift.instRingA_physics_1,
  GUT.WeylHiggsInternalLift.radial_relation => Physics.WeylHiggsInternalLift.radial_relation,
  GUT.WeylHiggsInternalLift.scalarProduct => Physics.WeylHiggsInternalLift.scalarProduct,
  GUT.WeylHiggsInternalLift.scalarProduct.eq_1 => Physics.WeylHiggsInternalLift.scalarProduct.eq_1,
  GUT.WeylHiggsInternalLift.scalar_product_zero => Physics.WeylHiggsInternalLift.scalar_product_zero,
  GUT.WeylHiggsInternalLift.second_word_scalar => Physics.WeylHiggsInternalLift.second_word_scalar
]

assert_compatible GUT.WeylHiggsInternalLift.derivative_four => Physics.WeylHiggsInternalLift.derivative_four
assert_compatible GUT.WeylHiggsInternalLift.derivative_zero => Physics.WeylHiggsInternalLift.derivative_zero
assert_compatible GUT.WeylHiggsInternalLift.first_word_scalar => Physics.WeylHiggsInternalLift.first_word_scalar
assert_compatible GUT.WeylHiggsInternalLift.instAddCommGroupA_physics_1 => Physics.WeylHiggsInternalLift.instAddCommGroupA_physics_1
assert_compatible GUT.WeylHiggsInternalLift.instModuleComplexA_physics_1 => Physics.WeylHiggsInternalLift.instModuleComplexA_physics_1
assert_compatible GUT.WeylHiggsInternalLift.instRingA_physics_1 => Physics.WeylHiggsInternalLift.instRingA_physics_1
assert_compatible GUT.WeylHiggsInternalLift.radial_relation => Physics.WeylHiggsInternalLift.radial_relation
assert_compatible GUT.WeylHiggsInternalLift.scalarProduct => Physics.WeylHiggsInternalLift.scalarProduct
assert_compatible GUT.WeylHiggsInternalLift.scalarProduct.eq_1 => Physics.WeylHiggsInternalLift.scalarProduct.eq_1
assert_compatible GUT.WeylHiggsInternalLift.scalar_product_zero => Physics.WeylHiggsInternalLift.scalar_product_zero
assert_compatible GUT.WeylHiggsInternalLift.second_word_scalar => Physics.WeylHiggsInternalLift.second_word_scalar
