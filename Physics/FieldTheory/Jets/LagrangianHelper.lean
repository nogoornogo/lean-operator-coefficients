import Physics.FieldTheory.Jets.Lagrangian.LagrangianHelper
import Math.Algebra.LagrangianControls
import Physics.FieldTheory.Jets.ScalarInputAdapter
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.LagrangianHelper instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarLagrangianHelper.E => Physics.ScalarLagrangianHelper.E,
  GUT.ScalarLagrangianHelper.density => Physics.ScalarLagrangianHelper.density,
  GUT.ScalarLagrangianHelper.density.eq_1 => Physics.ScalarLagrangianHelper.density.eq_1,
  GUT.ScalarLagrangianHelper.density_eval => Physics.ScalarLagrangianHelper.density_eval,
  GUT.ScalarLagrangianHelper.directionalKinetic => Physics.ScalarLagrangianHelper.directionalKinetic,
  GUT.ScalarLagrangianHelper.directionalKinetic.eq_1 => Physics.ScalarLagrangianHelper.directionalKinetic.eq_1,
  GUT.ScalarLagrangianHelper.directional_euler => Physics.ScalarLagrangianHelper.directional_euler,
  GUT.ScalarLagrangianHelper.extraction => Physics.ScalarLagrangianHelper.extraction,
  GUT.ScalarLagrangianHelper.first_variation_zero => Physics.ScalarLagrangianHelper.first_variation_zero,
  GUT.ScalarLagrangianHelper.generated_equation => Physics.ScalarLagrangianHelper.generated_equation,
  GUT.ScalarLagrangianHelper.generated_invariant => Physics.ScalarLagrangianHelper.generated_invariant,
  GUT.ScalarLagrangianHelper.ideal_stable => Physics.ScalarLagrangianHelper.ideal_stable,
  GUT.ScalarLagrangianHelper.input => Physics.ScalarLagrangianHelper.input,
  GUT.ScalarLagrangianHelper.kinetic => Physics.ScalarLagrangianHelper.kinetic,
  GUT.ScalarLagrangianHelper.kinetic.eq_1 => Physics.ScalarLagrangianHelper.kinetic.eq_1,
  GUT.ScalarLagrangianHelper.kinetic_euler => Physics.ScalarLagrangianHelper.kinetic_euler,
  GUT.ScalarLagrangianHelper.phi => Physics.ScalarLagrangianHelper.phi,
  GUT.ScalarLagrangianHelper.stable => Physics.ScalarLagrangianHelper.stable
]

assert_compatible GUT.ScalarLagrangianHelper.E => Physics.ScalarLagrangianHelper.E
assert_compatible GUT.ScalarLagrangianHelper.density => Physics.ScalarLagrangianHelper.density
assert_compatible GUT.ScalarLagrangianHelper.density.eq_1 => Physics.ScalarLagrangianHelper.density.eq_1
assert_compatible GUT.ScalarLagrangianHelper.density_eval => Physics.ScalarLagrangianHelper.density_eval
assert_compatible GUT.ScalarLagrangianHelper.directionalKinetic => Physics.ScalarLagrangianHelper.directionalKinetic
assert_compatible GUT.ScalarLagrangianHelper.directionalKinetic.eq_1 => Physics.ScalarLagrangianHelper.directionalKinetic.eq_1
assert_compatible GUT.ScalarLagrangianHelper.directional_euler => Physics.ScalarLagrangianHelper.directional_euler
assert_compatible GUT.ScalarLagrangianHelper.extraction => Physics.ScalarLagrangianHelper.extraction
assert_compatible GUT.ScalarLagrangianHelper.first_variation_zero => Physics.ScalarLagrangianHelper.first_variation_zero
assert_compatible GUT.ScalarLagrangianHelper.generated_equation => Physics.ScalarLagrangianHelper.generated_equation
assert_compatible GUT.ScalarLagrangianHelper.generated_invariant => Physics.ScalarLagrangianHelper.generated_invariant
assert_compatible GUT.ScalarLagrangianHelper.ideal_stable => Physics.ScalarLagrangianHelper.ideal_stable
assert_compatible GUT.ScalarLagrangianHelper.input => Physics.ScalarLagrangianHelper.input
assert_compatible GUT.ScalarLagrangianHelper.kinetic => Physics.ScalarLagrangianHelper.kinetic
assert_compatible GUT.ScalarLagrangianHelper.kinetic.eq_1 => Physics.ScalarLagrangianHelper.kinetic.eq_1
assert_compatible GUT.ScalarLagrangianHelper.kinetic_euler => Physics.ScalarLagrangianHelper.kinetic_euler
assert_compatible GUT.ScalarLagrangianHelper.phi => Physics.ScalarLagrangianHelper.phi
assert_compatible GUT.ScalarLagrangianHelper.stable => Physics.ScalarLagrangianHelper.stable
