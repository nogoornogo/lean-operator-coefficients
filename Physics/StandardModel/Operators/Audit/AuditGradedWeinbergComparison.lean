import Physics.StandardModel.Operators.GradedWeinbergComparison

/-! Strict transitive audit of the actual LLHH generic-quotient consumer. -/
open Lean in
run_cmd do
  let ds := [
    ``GUT.GradedWeinbergComparison.leptonEquiv,
    ``GUT.GradedWeinbergComparison.higgsEquiv,
    ``GUT.GradedWeinbergComparison.domainEquiv,
    ``GUT.GradedWeinbergComparison.domainEquiv_pure,
    ``GUT.GradedWeinbergComparison.inputEquiv,
    ``GUT.GradedWeinbergComparison.inputEquiv_pure,
    ``GUT.GradedWeinbergComparison.equiv,
    ``GUT.GradedWeinbergComparison.onSMEquiv,
    ``GUT.GradedWeinbergComparison.onSMEquiv_def,
    ``GUT.GradedWeinbergComparison.comparison,
    ``GUT.GradedWeinbergComparison.extraction_commutes,
    ``GUT.GradedWeinbergComparison.reconstruction_commutes,
    ``GUT.GradedWeinbergComparison.reconstruct_extract,
    ``GUT.GradedWeinbergComparison.extract_reconstruct,
    ``GUT.GradedWeinbergComparison.forbidden_iff,
    ``GUT.GradedWeinbergComparison.nonzero_iff,
    ``GUT.GradedWeinbergComparison.oneGenerationEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded LLHH comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded LLHH comparison: {ds.length} strict transitive checks passed"
