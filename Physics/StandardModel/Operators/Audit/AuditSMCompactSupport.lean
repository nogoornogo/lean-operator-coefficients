import Math.RepresentationTheory.Audit.AuditCompactGenerationOccupations
import Physics.StandardModel.Operators.Audit.AuditSMStructuralSupport
import Physics.StandardModel.Operators.SMCompactSupportExamples

run_cmd do
  let ds := [
    ``GUT.SMCompactSupportDecision.su2Decision,
    ``GUT.SMCompactSupportDecision.ownerEq,
    ``GUT.SMCompactSupportDecision.positiveDecision,
    ``GUT.SMCompactSupportDecision.negativeDecision,
    ``GUT.SMCompactSupportDecision.diagramDecision,
    ``GUT.SMCompactSupportDecision.colorDecision,
    ``GUT.SMCompactSupportDecision.jointDecision,
    ``GUT.SMCompactSupportDecision.expressionDecision,
    ``GUT.SMCompactSupportDecision.contentDecision,
    ``GUT.SMCompactSupportDecision.higgsDecision]
  let ds := ds ++ [``GUT.SMCompactSupportExamples.q18Allowed,
    ``GUT.SMCompactSupportExamples.mixedForbidden]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "compact support audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"compact support: {ds.length} strict transitive checks passed"
