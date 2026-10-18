import Physics.StandardModel.Operators.GradedBnvComparison

/-! Strict transitive audit of actual SM inputs and degree-six/seven comparison diagrams. -/
open Lean in
run_cmd do
  let ds := [
    ``GUT.GradedBnvComparison.fermion_eq,
    ``GUT.GradedBnvComparison.boson_eq,
    ``GUT.GradedBnvComparison.stable,
    ``GUT.GradedBnvComparison.supportPresentation,
    ``GUT.GradedBnvComparison.supportEquiv,
    ``GUT.GradedBnvComparison.perDegreeEquiv,
    ``GUT.GradedBnvComparison.sixComparison,
    ``GUT.GradedBnvComparison.sevenComparison,
    ``GUT.GradedBnvComparison.boundedSevenEquiv,
    ``GUT.GradedBnvComparison.comparison,
    ``GUT.GradedBnvComparison.extraction_commutes,
    ``GUT.GradedBnvComparison.reconstruction_commutes,
    ``GUT.GradedBnvComparison.reconstruct_extract,
    ``GUT.GradedBnvComparison.extract_reconstruct,
    ``GUT.GradedBnvComparison.forbidden_iff,
    ``GUT.GradedBnvComparison.nonzero_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded BNV comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded BNV comparison: {ds.length} strict transitive checks passed"
