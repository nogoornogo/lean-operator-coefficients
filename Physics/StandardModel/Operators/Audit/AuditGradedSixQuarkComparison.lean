import Physics.StandardModel.Operators.GradedSixQuarkComparison

/-! Strict transitive audit of the actual u²d⁴ generic-quotient consumer. -/
open Lean in
run_cmd do
  let ds := [
    ``GUT.GradedSixQuarkComparison.field_apply,
    ``GUT.GradedSixQuarkComparison.emptyEquiv,
    ``GUT.GradedSixQuarkComparison.emptyEquiv_symm_apply,
    ``GUT.GradedSixQuarkComparison.toOrdered,
    ``GUT.GradedSixQuarkComparison.fromOrdered,
    ``GUT.GradedSixQuarkComparison.orderedEquiv,
    ``GUT.GradedSixQuarkComparison.equiv,
    ``GUT.GradedSixQuarkComparison.equiv_def,
    ``GUT.GradedSixQuarkComparison.comparison,
    ``GUT.GradedSixQuarkComparison.extraction_commutes,
    ``GUT.GradedSixQuarkComparison.reconstruction_commutes,
    ``GUT.GradedSixQuarkComparison.reconstruct_extract,
    ``GUT.GradedSixQuarkComparison.extract_reconstruct,
    ``GUT.GradedSixQuarkComparison.forbidden_iff,
    ``GUT.GradedSixQuarkComparison.nonzero_iff,
    ``GUT.GradedSixQuarkComparison.oneGenerationEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded six-quark comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded six-quark comparison: {ds.length} strict transitive checks passed"
