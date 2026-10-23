import Math.RepresentationTheory.Exterior.Audit.AuditCompactGenerationOccupations
import Physics.StandardModel.Operators.Support.Coordinates.Audit.AuditSMStructuralSupport
import Physics.StandardModel.Operators.Support.Decomposition.SMCompactSupportExamples

run_cmd do
  let ds := [
    ``Physics.SMCompactSupportDecision.su2Decision,
    ``Physics.SMCompactSupportDecision.ownerEq,
    ``Physics.SMCompactSupportDecision.positiveDecision,
    ``Physics.SMCompactSupportDecision.negativeDecision,
    ``Physics.SMCompactSupportDecision.diagramDecision,
    ``Physics.SMCompactSupportDecision.colorDecision,
    ``Physics.SMCompactSupportDecision.jointDecision,
    ``Physics.SMCompactSupportDecision.expressionDecision,
    ``Physics.SMCompactSupportDecision.contentDecision,
    ``Physics.SMCompactSupportDecision.higgsDecision]
  let ds := ds ++ [``Physics.SMCompactSupportExamples.q18Allowed,
    ``Physics.SMCompactSupportExamples.mixedForbidden]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "compact support audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"compact support: {ds.length} strict transitive checks passed"
