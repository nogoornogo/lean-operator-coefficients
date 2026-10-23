import Physics.StandardModel.Operators.Weinberg.GradedWeinbergComparison

/-! Strict transitive audit of the actual LLHH generic-quotient consumer. -/
open Lean in
run_cmd do
  let ds := [
    ``Physics.GradedWeinbergComparison.leptonEquiv,
    ``Physics.GradedWeinbergComparison.higgsEquiv,
    ``Physics.GradedWeinbergComparison.domainEquiv,
    ``Physics.GradedWeinbergComparison.domainEquiv_pure,
    ``Physics.GradedWeinbergComparison.inputEquiv,
    ``Physics.GradedWeinbergComparison.inputEquiv_pure,
    ``Physics.GradedWeinbergComparison.equiv,
    ``Physics.GradedWeinbergComparison.onSMEquiv,
    ``Physics.GradedWeinbergComparison.onSMEquiv_def,
    ``Physics.GradedWeinbergComparison.comparison,
    ``Physics.GradedWeinbergComparison.extraction_commutes,
    ``Physics.GradedWeinbergComparison.reconstruction_commutes,
    ``Physics.GradedWeinbergComparison.reconstruct_extract,
    ``Physics.GradedWeinbergComparison.extract_reconstruct,
    ``Physics.GradedWeinbergComparison.forbidden_iff,
    ``Physics.GradedWeinbergComparison.nonzero_iff,
    ``Physics.GradedWeinbergComparison.oneGenerationEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Graded LLHH comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Graded LLHH comparison: {ds.length} strict transitive checks passed"
