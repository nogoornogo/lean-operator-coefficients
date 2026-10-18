import Math.Audit.ImportOrigin
import Math.RepresentationTheory.InvariantProtection
import Math.RepresentationTheory.GradedSymmetryProtection
import Math.RepresentationTheory.MixedScalarSelection
import Math.RepresentationTheory.MixedChargeSelection
import Math.RepresentationTheory.PolynomialCovariantEvaluation
import Math.RepresentationTheory.SymmetryProtectionExamples

/-! Persistent strict transitive audit of all-degree protection and polynomial evaluation. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Symmetry protection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.InvariantProtection.Protected,
    ``Math.InvariantProtection.protected_iff_surjective,
    ``Math.InvariantProtection.selector_zero_iff,
    ``Math.InvariantProtection.family_surjective_iff,
    ``Math.InvariantProtection.finite_support_surjective_iff,
    ``Math.InvariantProtection.finite_support_forbidden_iff,
    ``Math.InvariantProtection.product_forbidden_iff,
    ``Math.InvariantProtection.square_surjective_iff,
    ``Math.GradedSymmetryProtection.Protected,
    ``Math.GradedSymmetryProtection.protected_iff_surjective,
    ``Math.GradedSymmetryProtection.protected_iff_residual_surjective,
    ``Math.GradedSymmetryProtection.all_protected_iff_input_surjective,
    ``Math.GradedSymmetryProtection.all_protected_iff_hom_surjective,
    ``Math.GradedSymmetryProtection.protected_iff_factors,
    ``Math.GradedSymmetryProtection.all_protected_iff_finite_support_surjective,
    ``Math.GradedSymmetryProtection.all_bounds_protected_iff,
    ``Math.MixedScalarSelection.invariant_zero,
    ``Math.MixedScalarSelection.quotient_scalar,
    ``Math.MixedScalarSelection.tensor_scalar,
    ``Math.MixedScalarSelection.ordered_scalar,
    ``Math.MixedScalarSelection.base_scalar,
    ``Math.MixedScalarSelection.residual_scalar,
    ``Math.MixedScalarSelection.factor_zero,
    ``Math.MixedScalarSelection.nonzero_neutral,
    ``Math.MixedScalarSelection.local_factor_zero,
    ``Math.MixedScalarSelection.all_forbidden,
    ``Math.MixedScalarSelection.all_hom_forbidden,
    ``Math.MixedChargeSelection.charge_stable,
    ``Math.MixedChargeSelection.total_eq_character,
    ``Math.MixedChargeSelection.charge_zero,
    ``Math.MixedChargeSelection.conjugate_charge,
    ``Math.MixedChargeSelection.all_forbidden,
    ``Math.MixedChargeSelection.cyclic_detect_iff,
    ``Math.PolynomialCovariantEvaluation.covariants,
    ``Math.PolynomialCovariantEvaluation.stabilizer,
    ``Math.PolynomialCovariantEvaluation.evaluation,
    ``Math.PolynomialCovariantEvaluation.constant,
    ``Math.PolynomialCovariantEvaluation.trivial_target_surjective,
    ``Math.PolynomialCovariantEvaluation.coordinate,
    ``Math.PolynomialCovariantEvaluation.scalar_nonzero_surjective,
    ``Math.PolynomialCovariantEvaluation.scalar_zero_evaluation,
    ``Math.SymmetryProtectionExamples.injective_unprotected,
    ``Math.SymmetryProtectionExamples.mixed_one_two_forbidden,
    ``Math.SymmetryProtectionExamples.neutral_local_zero,
    ``Math.SymmetryProtectionExamples.charge_vector,
    ``Math.SymmetryProtectionExamples.cyclic_conjugate]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Symmetry protection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Symmetry protection: {ds.length} strict transitive checks passed"
