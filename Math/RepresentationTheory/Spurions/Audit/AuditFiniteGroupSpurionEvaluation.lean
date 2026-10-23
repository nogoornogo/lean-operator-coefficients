import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Spurions.FiniteGroupSpurionCoefficients
import Math.RepresentationTheory.Spurions.FiniteGroupSpurionExamples

/-! Persistent layer and strict transitive axiom audit for finite-group evaluation. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Finite-group evaluation imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.PolynomialCovariantEvaluation.exists_separator,
    ``Math.PolynomialCovariantEvaluation.exists_delta,
    ``Math.PolynomialCovariantEvaluation.finite_interpolation,
    ``Math.PolynomialCovariantEvaluation.linearCoordinates,
    ``Math.PolynomialCovariantEvaluation.eval_linearCoordinates,
    ``Math.PolynomialCovariantEvaluation.precompose,
    ``Math.PolynomialCovariantEvaluation.evaluate_precompose,
    ``Math.PolynomialCovariantEvaluation.postcompose,
    ``Math.PolynomialCovariantEvaluation.evaluate_postcompose,
    ``Math.PolynomialCovariantEvaluation.reynolds,
    ``Math.PolynomialCovariantEvaluation.evaluate_reynolds,
    ``Math.PolynomialCovariantEvaluation.reynolds_covariant,
    ``Math.PolynomialCovariantEvaluation.orbit_factors,
    ``Math.PolynomialCovariantEvaluation.finite_group_surjective,
    ``Math.PolynomialCovariantEvaluation.coordinateAction,
    ``Math.PolynomialCovariantEvaluation.coordinate_stabilizer,
    ``Math.PolynomialCovariantEvaluation.fixedDualEquiv,
    ``Math.PolynomialCovariantEvaluation.coefficientEvaluation,
    ``Math.PolynomialCovariantEvaluation.coefficientEvaluation_surjective,
    ``Math.PolynomialCovariantEvaluation.finite_dimensional_coefficients,
    ``Math.PolynomialCovariantEvaluation.nonzero_coefficient_iff,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.action,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.value_injective,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.value_stabilizer,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.free_value_evaluation,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.zero_evaluation_equal,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.free_attains_value,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.zero_attains_constant,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.zero_not_attains_value]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite-group evaluation {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite-group evaluation: {ds.length} strict transitive checks passed"
