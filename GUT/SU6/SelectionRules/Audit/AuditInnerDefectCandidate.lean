import GUT.SU6.SelectionRules.Models.InnerDefectCandidate
open Lean in
run_cmd do
  let ds := [
    ``GUT.InnerDefectCandidate.light_mul_iff,
    ``GUT.InnerDefectCandidate.lightRepresentation,
    ``GUT.InnerDefectCandidate.lightRepresentation_commutes]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Inner defect {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Inner defect: {ds.length} strict transitive checks passed"
