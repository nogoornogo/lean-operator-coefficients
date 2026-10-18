import GUT.SU6.SelectionRules.Models.TargetIndexCompatibility
open Lean in
run_cmd do
  let ds := [
    ``GUT.TargetIndexCompatibility.target_index_invariant,
    ``GUT.TargetIndexCompatibility.no_positive_target_of_mismatch,
    ``GUT.TargetIndexCompatibility.no_sm_positive_target_of_mismatch]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dual index {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dual index: {ds.length} strict transitive checks passed"
