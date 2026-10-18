import GUT.SU6.SelectionRules.Models.GaugeEquivalentCandidate
open Lean in
run_cmd do
  let ds := [
    ``GUT.GaugeEquivalentCandidate.removed_projection,
    ``GUT.GaugeEquivalentCandidate.forbidden_iff,
    ``GUT.GaugeEquivalentCandidate.input_forbidden_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Gauge comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Gauge comparison: {ds.length} strict transitive checks passed"
