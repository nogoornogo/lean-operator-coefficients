import GUT.SU6.SelectionRules.Models.PairedAdjointCandidate
open Lean in
run_cmd do
  let ds := [``GUT.PairedAdjointCandidate.conjugate_mul, ``GUT.PairedAdjointCandidate.conjugate_one, ``GUT.PairedAdjointCandidate.fourth_power, ``GUT.PairedAdjointCandidate.pairedVacuum_fixed, ``GUT.PairedAdjointCandidate.colorMatrix_specialUnitary, ``GUT.PairedAdjointCandidate.color_tail_rows, ``GUT.PairedAdjointCandidate.color_fixes_first, ``GUT.PairedAdjointCandidate.color_does_not_fix_second, ``GUT.PairedAdjointCandidate.color_does_not_fix_pair]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Paired adjoint {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Paired adjoint: {ds.length} strict transitive checks passed"
