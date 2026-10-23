import Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationIBP
import Physics.FieldTheory.Jets.WeylEquationControls
import Math.RepresentationTheory.LinearJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Weyl.Equations.WeylEquationIBP instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylLinearEquation.Algebra => Physics.WeylLinearEquation.Algebra,
  GUT.WeylLinearEquation.algebraAction => Physics.WeylLinearEquation.algebraAction,
  GUT.WeylLinearEquation.coefficientEquiv => Physics.WeylLinearEquation.coefficientEquiv,
  GUT.WeylLinearEquation.detect => Physics.WeylLinearEquation.detect,
  GUT.WeylLinearEquation.detect.eq_1 => Physics.WeylLinearEquation.detect.eq_1,
  GUT.WeylLinearEquation.equation_descendant_zero => Physics.WeylLinearEquation.equation_descendant_zero,
  GUT.WeylLinearEquation.equation_zero => Physics.WeylLinearEquation.equation_zero,
  GUT.WeylLinearEquation.finite_source => Physics.WeylLinearEquation.finite_source,
  GUT.WeylLinearEquation.higher_mixed_jet_survives => Physics.WeylLinearEquation.higher_mixed_jet_survives,
  GUT.WeylLinearEquation.projection => Physics.WeylLinearEquation.projection,
  GUT.WeylLinearEquation.projection_derivative => Physics.WeylLinearEquation.projection_derivative,
  GUT.WeylLinearEquation.sourceEquiv => Physics.WeylLinearEquation.sourceEquiv,
  GUT.WeylLinearEquation.spectatorEquations => Physics.WeylLinearEquation.spectatorEquations,
  GUT.WeylLinearEquation.spectatorSeed => Physics.WeylLinearEquation.spectatorSeed,
  GUT.WeylLinearEquation.spectatorSeed.eq_1 => Physics.WeylLinearEquation.spectatorSeed.eq_1,
  GUT.WeylLinearEquation.spectator_covariant => Physics.WeylLinearEquation.spectator_covariant
]

assert_compatible GUT.WeylLinearEquation.Algebra => Physics.WeylLinearEquation.Algebra
assert_compatible GUT.WeylLinearEquation.algebraAction => Physics.WeylLinearEquation.algebraAction
assert_compatible GUT.WeylLinearEquation.coefficientEquiv => Physics.WeylLinearEquation.coefficientEquiv
assert_compatible GUT.WeylLinearEquation.detect => Physics.WeylLinearEquation.detect
assert_compatible GUT.WeylLinearEquation.detect.eq_1 => Physics.WeylLinearEquation.detect.eq_1
assert_compatible GUT.WeylLinearEquation.equation_descendant_zero => Physics.WeylLinearEquation.equation_descendant_zero
assert_compatible GUT.WeylLinearEquation.equation_zero => Physics.WeylLinearEquation.equation_zero
assert_compatible GUT.WeylLinearEquation.finite_source => Physics.WeylLinearEquation.finite_source
assert_compatible GUT.WeylLinearEquation.higher_mixed_jet_survives => Physics.WeylLinearEquation.higher_mixed_jet_survives
assert_compatible GUT.WeylLinearEquation.projection => Physics.WeylLinearEquation.projection
assert_compatible GUT.WeylLinearEquation.projection_derivative => Physics.WeylLinearEquation.projection_derivative
assert_compatible GUT.WeylLinearEquation.sourceEquiv => Physics.WeylLinearEquation.sourceEquiv
assert_compatible GUT.WeylLinearEquation.spectatorEquations => Physics.WeylLinearEquation.spectatorEquations
assert_compatible GUT.WeylLinearEquation.spectatorSeed => Physics.WeylLinearEquation.spectatorSeed
assert_compatible GUT.WeylLinearEquation.spectatorSeed.eq_1 => Physics.WeylLinearEquation.spectatorSeed.eq_1
assert_compatible GUT.WeylLinearEquation.spectator_covariant => Physics.WeylLinearEquation.spectator_covariant
