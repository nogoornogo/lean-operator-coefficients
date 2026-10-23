import GUT.SU6.SelectionRules.Models.ChargeReversingCandidate
import Math.RepresentationTheory.Invariants.Audit.AuditCovariantCharacterObstruction
import Physics.StandardModel.Spectrum.Representations.Audit.AuditHyperchargeReversalProbe
open Lean in
run_cmd do
  let ds := [``GUT.ChargeReversingCandidate.light_dual_index_zero,
    ``GUT.ChargeReversingCandidate.no_positive_target,
    ``GUT.ChargeReversingCandidate.no_sm_positive_target,
    ``GUT.ChargeReversingCandidate.no_positive_target_of_conjugate_inverse,
    ``GUT.ChargeReversingCandidate.no_sm_positive_target_of_conjugate_inverse]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Reversing candidate {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Reversing candidate: {ds.length} strict transitive checks passed"
