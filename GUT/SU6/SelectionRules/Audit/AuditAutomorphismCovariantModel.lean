import GUT.SU6.SelectionRules.Models.AutomorphismCovariantModel
import Math.RepresentationTheory.Invariants.Audit.AuditAutomorphismCovariantHom

/-! Strict transitive audit of the noncommuting SU(6) model interface. -/
open Lean in
run_cmd do
  let ds := [
    ``GUT.AutomorphismCovariantModel.Model,
    ``GUT.AutomorphismCovariantModel.radical_stable,
    ``GUT.AutomorphismCovariantModel.lightResidualSubrepresentation,
    ``GUT.AutomorphismCovariantModel.gauge_covariance,
    ``GUT.AutomorphismCovariantModel.lightAction,
    ``GUT.AutomorphismCovariantModel.lightEquiv,
    ``GUT.AutomorphismCovariantModel.HasDualTarget,
    ``GUT.AutomorphismCovariantModel.HasPositiveDualTarget,
    ``GUT.AutomorphismCovariantModel.HasResolvedDualTarget,
    ``GUT.AutomorphismCovariantModel.coefficientEquiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Covariant SU6 model {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Covariant SU6 model: {ds.length} strict transitive checks passed"
