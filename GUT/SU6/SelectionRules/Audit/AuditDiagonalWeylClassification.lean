import GUT.SU6.SelectionRules.Models.DiagonalWeylClassification
open Lean in
run_cmd do
  let ds := [``GUT.DiagonalWeylClassification.fixed_iff, ``GUT.DiagonalWeylClassification.split_fixed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Diagonal Weyl {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Diagonal Weyl: {ds.length} strict transitive checks passed"
