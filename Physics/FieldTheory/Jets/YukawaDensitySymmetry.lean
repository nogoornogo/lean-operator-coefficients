import Physics.FieldTheory.Jets.Lagrangian.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.YukawaModel
import Math.RepresentationTheory.PairedJetContractions
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.YukawaDensitySymmetry instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.YukawaModel.density_invariant => Physics.YukawaModel.density_invariant,
  GUT.YukawaModel.fermion_kinetic_invariant => Physics.YukawaModel.fermion_kinetic_invariant,
  GUT.YukawaModel.instAddCommGroupA_physics_1 => Physics.YukawaModel.instAddCommGroupA_physics_1,
  GUT.YukawaModel.instModuleComplexA_physics_1 => Physics.YukawaModel.instModuleComplexA_physics_1,
  GUT.YukawaModel.instRingA_physics_1 => Physics.YukawaModel.instRingA_physics_1,
  GUT.YukawaModel.kineticContraction => Physics.YukawaModel.kineticContraction,
  GUT.YukawaModel.kineticContraction_covariant => Physics.YukawaModel.kineticContraction_covariant,
  GUT.YukawaModel.kineticTerm_eval => Physics.YukawaModel.kineticTerm_eval,
  GUT.YukawaModel.kinetic_expansion => Physics.YukawaModel.kinetic_expansion,
  GUT.YukawaModel.scalarFieldInclusion => Physics.YukawaModel.scalarFieldInclusion,
  GUT.YukawaModel.scalarFieldInclusion.eq_1 => Physics.YukawaModel.scalarFieldInclusion.eq_1,
  GUT.YukawaModel.scalarInclusion => Physics.YukawaModel.scalarInclusion,
  GUT.YukawaModel.scalarInclusion.eq_1 => Physics.YukawaModel.scalarInclusion.eq_1,
  GUT.YukawaModel.scalarInclusion_X => Physics.YukawaModel.scalarInclusion_X,
  GUT.YukawaModel.scalarInclusion_natural => Physics.YukawaModel.scalarInclusion_natural,
  GUT.YukawaModel.scalar_kinetic_expansion => Physics.YukawaModel.scalar_kinetic_expansion,
  GUT.YukawaModel.scalar_kinetic_invariant => Physics.YukawaModel.scalar_kinetic_invariant
]

assert_compatible GUT.YukawaModel.density_invariant => Physics.YukawaModel.density_invariant
assert_compatible GUT.YukawaModel.fermion_kinetic_invariant => Physics.YukawaModel.fermion_kinetic_invariant
assert_compatible GUT.YukawaModel.instAddCommGroupA_physics_1 => Physics.YukawaModel.instAddCommGroupA_physics_1
assert_compatible GUT.YukawaModel.instModuleComplexA_physics_1 => Physics.YukawaModel.instModuleComplexA_physics_1
assert_compatible GUT.YukawaModel.instRingA_physics_1 => Physics.YukawaModel.instRingA_physics_1
assert_compatible GUT.YukawaModel.kineticContraction => Physics.YukawaModel.kineticContraction
assert_compatible GUT.YukawaModel.kineticContraction_covariant => Physics.YukawaModel.kineticContraction_covariant
assert_compatible GUT.YukawaModel.kineticTerm_eval => Physics.YukawaModel.kineticTerm_eval
assert_compatible GUT.YukawaModel.kinetic_expansion => Physics.YukawaModel.kinetic_expansion
assert_compatible GUT.YukawaModel.scalarFieldInclusion => Physics.YukawaModel.scalarFieldInclusion
assert_compatible GUT.YukawaModel.scalarFieldInclusion.eq_1 => Physics.YukawaModel.scalarFieldInclusion.eq_1
assert_compatible GUT.YukawaModel.scalarInclusion => Physics.YukawaModel.scalarInclusion
assert_compatible GUT.YukawaModel.scalarInclusion.eq_1 => Physics.YukawaModel.scalarInclusion.eq_1
assert_compatible GUT.YukawaModel.scalarInclusion_X => Physics.YukawaModel.scalarInclusion_X
assert_compatible GUT.YukawaModel.scalarInclusion_natural => Physics.YukawaModel.scalarInclusion_natural
assert_compatible GUT.YukawaModel.scalar_kinetic_expansion => Physics.YukawaModel.scalar_kinetic_expansion
assert_compatible GUT.YukawaModel.scalar_kinetic_invariant => Physics.YukawaModel.scalar_kinetic_invariant
