import GUT.SU6.SelectionRules.Models.CovariantFourFermion
import Math.RepresentationTheory.Audit.AuditCovariantExterior

open Lean in
run_cmd do
  let ds := [
    ``GUT.CovariantFourFermion.exteriorAction,
    ``GUT.CovariantFourFermion.equiv,
    ``GUT.CovariantFourFermion.forbidden_iff,
    ``GUT.CovariantFourFermion.inputEquiv,
    ``GUT.CovariantFourFermion.input_forbidden_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Covariant four fermion {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Covariant four fermion: {ds.length} strict transitive checks passed"
