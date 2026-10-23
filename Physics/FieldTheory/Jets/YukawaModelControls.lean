import Physics.FieldTheory.Jets.Lagrangian.YukawaModelControls
import Physics.FieldTheory.Jets.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.RegisteredLagrangianModels
import Math.Algebra.MixedJetPairCoordinates
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.YukawaModelControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.YukawaModel.spin.eq_1 => Physics.YukawaModel.spin.eq_1,
  GUT.YukawaModelControls.boost => Physics.YukawaModelControls.boost,
  GUT.YukawaModelControls.boost.eq_1 => Physics.YukawaModelControls.boost.eq_1,
  GUT.YukawaModelControls.boost_component => Physics.YukawaModelControls.boost_component,
  GUT.YukawaModelControls.free_odd_recovery => Physics.YukawaModelControls.free_odd_recovery,
  GUT.YukawaModelControls.free_scalar_recovery => Physics.YukawaModelControls.free_scalar_recovery,
  GUT.YukawaModelControls.instAddCommGroupA_physics => Physics.YukawaModelControls.instAddCommGroupA_physics,
  GUT.YukawaModelControls.instModuleComplexA_physics => Physics.YukawaModelControls.instModuleComplexA_physics,
  GUT.YukawaModelControls.instRingA_physics => Physics.YukawaModelControls.instRingA_physics,
  GUT.YukawaModelControls.nonScalar => Physics.YukawaModelControls.nonScalar,
  GUT.YukawaModelControls.nonScalar.eq_1 => Physics.YukawaModelControls.nonScalar.eq_1,
  GUT.YukawaModelControls.nonScalar_probe => Physics.YukawaModelControls.nonScalar_probe,
  GUT.YukawaModelControls.nonScalar_transform => Physics.YukawaModelControls.nonScalar_transform,
  GUT.YukawaModelControls.pairProbe => Physics.YukawaModelControls.pairProbe,
  GUT.YukawaModelControls.pairProbe.eq_1 => Physics.YukawaModelControls.pairProbe.eq_1,
  GUT.YukawaModelControls.quartic_nonzero_forbids => Physics.YukawaModelControls.quartic_nonzero_forbids,
  GUT.YukawaModelControls.quartic_zero_allows => Physics.YukawaModelControls.quartic_zero_allows,
  GUT.YukawaModelControls.scalar_target_identity => Physics.YukawaModelControls.scalar_target_identity,
  GUT.YukawaModelControls.spectator_equation => Physics.YukawaModelControls.spectator_equation,
  GUT.YukawaModelControls.symmetry_breaking_control => Physics.YukawaModelControls.symmetry_breaking_control
]

assert_compatible GUT.YukawaModel.spin.eq_1 => Physics.YukawaModel.spin.eq_1
assert_compatible GUT.YukawaModelControls.boost => Physics.YukawaModelControls.boost
assert_compatible GUT.YukawaModelControls.boost.eq_1 => Physics.YukawaModelControls.boost.eq_1
assert_compatible GUT.YukawaModelControls.boost_component => Physics.YukawaModelControls.boost_component
assert_compatible GUT.YukawaModelControls.free_odd_recovery => Physics.YukawaModelControls.free_odd_recovery
assert_compatible GUT.YukawaModelControls.free_scalar_recovery => Physics.YukawaModelControls.free_scalar_recovery
assert_compatible GUT.YukawaModelControls.instAddCommGroupA_physics => Physics.YukawaModelControls.instAddCommGroupA_physics
assert_compatible GUT.YukawaModelControls.instModuleComplexA_physics => Physics.YukawaModelControls.instModuleComplexA_physics
assert_compatible GUT.YukawaModelControls.instRingA_physics => Physics.YukawaModelControls.instRingA_physics
assert_compatible GUT.YukawaModelControls.nonScalar => Physics.YukawaModelControls.nonScalar
assert_compatible GUT.YukawaModelControls.nonScalar.eq_1 => Physics.YukawaModelControls.nonScalar.eq_1
assert_compatible GUT.YukawaModelControls.nonScalar_probe => Physics.YukawaModelControls.nonScalar_probe
assert_compatible GUT.YukawaModelControls.nonScalar_transform => Physics.YukawaModelControls.nonScalar_transform
assert_compatible GUT.YukawaModelControls.pairProbe => Physics.YukawaModelControls.pairProbe
assert_compatible GUT.YukawaModelControls.pairProbe.eq_1 => Physics.YukawaModelControls.pairProbe.eq_1
assert_compatible GUT.YukawaModelControls.quartic_nonzero_forbids => Physics.YukawaModelControls.quartic_nonzero_forbids
assert_compatible GUT.YukawaModelControls.quartic_zero_allows => Physics.YukawaModelControls.quartic_zero_allows
assert_compatible GUT.YukawaModelControls.scalar_target_identity => Physics.YukawaModelControls.scalar_target_identity
assert_compatible GUT.YukawaModelControls.spectator_equation => Physics.YukawaModelControls.spectator_equation
assert_compatible GUT.YukawaModelControls.symmetry_breaking_control => Physics.YukawaModelControls.symmetry_breaking_control
