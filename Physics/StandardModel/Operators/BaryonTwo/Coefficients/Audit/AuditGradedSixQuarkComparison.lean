import Physics.StandardModel.Operators.BaryonTwo.Coefficients.GradedSixQuarkComparison

/-! Strict transitive audit of the actual u²d⁴ generic-quotient consumer. -/
open Lean in
run_cmd do
  let ds := [
    ``Physics.GradedSixQuarkComparison.field_apply,
    ``Physics.GradedSixQuarkComparison.emptyEquiv,
    ``Physics.GradedSixQuarkComparison.emptyEquiv_symm_apply,
    ``Physics.GradedSixQuarkComparison.toOrdered,
    ``Physics.GradedSixQuarkComparison.fromOrdered,
    ``Physics.GradedSixQuarkComparison.orderedEquiv,
    ``Physics.GradedSixQuarkComparison.equiv,
    ``Physics.GradedSixQuarkComparison.equiv_def,
    ``Physics.GradedSixQuarkComparison.comparison,
    ``Physics.GradedSixQuarkComparison.extraction_commutes,
    ``Physics.GradedSixQuarkComparison.reconstruction_commutes,
    ``Physics.GradedSixQuarkComparison.reconstruct_extract,
    ``Physics.GradedSixQuarkComparison.extract_reconstruct,
    ``Physics.GradedSixQuarkComparison.forbidden_iff,
    ``Physics.GradedSixQuarkComparison.nonzero_iff,
    ``Physics.GradedSixQuarkComparison.oneGenerationEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded six-quark comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded six-quark comparison: {ds.length} strict transitive checks passed"
