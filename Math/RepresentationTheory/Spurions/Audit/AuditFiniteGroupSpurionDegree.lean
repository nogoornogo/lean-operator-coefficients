import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Spurions.FiniteGroupSpurionDegreeExamples

/-! Strict transitive axiom and layer audit for finite-group degree bounds. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Finite-group degree imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.PolynomialCovariantEvaluation.DegreeLE,
    ``Math.PolynomialCovariantEvaluation.boundedCovariants,
    ``Math.PolynomialCovariantEvaluation.boundedEvaluation,
    ``Math.PolynomialCovariantEvaluation.exists_separator_bounded,
    ``Math.PolynomialCovariantEvaluation.exists_delta_bounded,
    ``Math.PolynomialCovariantEvaluation.finite_interpolation_bounded,
    ``Math.PolynomialCovariantEvaluation.totalDegree_bind_linear,
    ``Math.PolynomialCovariantEvaluation.linearCoordinates_degree,
    ``Math.PolynomialCovariantEvaluation.degreeLE_precompose,
    ``Math.PolynomialCovariantEvaluation.degreeLE_postcompose,
    ``Math.PolynomialCovariantEvaluation.orbitSize,
    ``Math.PolynomialCovariantEvaluation.orbitSize_pos,
    ``Math.PolynomialCovariantEvaluation.orbitSize_le_card,
    ``Math.PolynomialCovariantEvaluation.degreeLE_reynolds,
    ``Math.PolynomialCovariantEvaluation.finite_group_bounded,
    ``Math.PolynomialCovariantEvaluation.finite_group_card_bounded,
    ``Math.PolynomialCovariantEvaluation.boundedEvaluation_surjective,
    ``Math.PolynomialCovariantEvaluation.card_boundedEvaluation_surjective,
    ``Math.PolynomialCovariantEvaluation.orbitSize_zero,
    ``Math.PolynomialCovariantEvaluation.zero_degree_bounded,
    ``Math.PolynomialCovariantEvaluation.boundedCoefficientEvaluation,
    ``Math.PolynomialCovariantEvaluation.boundedCoefficientEvaluation_surjective,
    ``Math.PolynomialCovariantEvaluation.card_boundedCoefficientEvaluation_surjective,
    ``Math.PolynomialCovariantEvaluation.finite_dimensional_bounded_coefficients,
    ``Math.PolynomialCovariantEvaluation.degree_zero_evaluation_eq,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.free_value_degree_one,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.free_value_not_degree_zero,
    ``Math.PolynomialCovariantEvaluation.FiniteControls.zero_constant_degree_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Finite-group degree {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Finite-group degree: {ds.length} strict transitive checks passed"
