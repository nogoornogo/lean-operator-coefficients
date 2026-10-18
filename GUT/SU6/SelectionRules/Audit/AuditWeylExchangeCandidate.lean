import GUT.SU6.SelectionRules.Models.WeylExchangeCandidate
open Lean in
run_cmd do
  let ds := [
    ``GUT.WeylExchangeCandidate.vacuum_trace_zero,
    ``GUT.WeylExchangeCandidate.generator_fourth_power,
    ``GUT.WeylExchangeCandidate.generator_SU_fourth_power,
    ``GUT.WeylExchangeCandidate.diagonal_fixed_iff,
    ``GUT.WeylExchangeCandidate.split_not_fixed,
    ``GUT.WeylExchangeCandidate.vacuum_not_fixed]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weyl candidate {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weyl candidate: {ds.length} strict transitive checks passed"
