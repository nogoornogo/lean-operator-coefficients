import Physics.StandardModel.Operators.BaryonOne.Inputs.GradedBnvComparison

/-! Strict transitive audit of actual SM inputs and degree-six/seven comparison diagrams. -/
open Lean in
run_cmd do
  let ds := [
    ``Physics.GradedBnvComparison.fermion_eq,
    ``Physics.GradedBnvComparison.boson_eq,
    ``Physics.GradedBnvComparison.stable,
    ``Physics.GradedBnvComparison.supportPresentation,
    ``Physics.GradedBnvComparison.supportEquiv,
    ``Physics.GradedBnvComparison.perDegreeEquiv,
    ``Physics.GradedBnvComparison.sixComparison,
    ``Physics.GradedBnvComparison.sevenComparison,
    ``Physics.GradedBnvComparison.boundedSevenEquiv,
    ``Physics.GradedBnvComparison.comparison,
    ``Physics.GradedBnvComparison.extraction_commutes,
    ``Physics.GradedBnvComparison.reconstruction_commutes,
    ``Physics.GradedBnvComparison.reconstruct_extract,
    ``Physics.GradedBnvComparison.extract_reconstruct,
    ``Physics.GradedBnvComparison.forbidden_iff,
    ``Physics.GradedBnvComparison.nonzero_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded BNV comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded BNV comparison: {ds.length} strict transitive checks passed"
