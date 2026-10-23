import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteLeptonDegreeExamples
import Physics.StandardModel.Operators.Support.Dimension.Audit.AuditSMChargeDegreeBounds
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`Physics.SMFiniteLeptonDegreeBounds, `Physics.SMFiniteLeptonDegreeExamples]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "minimum lepton degree bound {name} uses unexpected axiom {ax}"
      count := count+1
  if count < 30 then
    throwError "minimum lepton degree audit found only {count} declarations"
  Lean.logInfo m!"minimum lepton degree bounds: {count} strict transitive checks passed"
