import Physics.StandardModel.Operators.SMFiniteLeptonSupportExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`GUT.SMLeptonChargeWitnesses, `GUT.SMFiniteLeptonSupport,
    `GUT.SMFiniteLeptonAssignments, `GUT.SMFiniteLeptonSupportExamples]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "finite lepton support {name} uses unexpected axiom {ax}"
      count := count+1
  if count < 277 then
    throwError "finite lepton support audit found only {count} declarations"
  Lean.logInfo m!"finite lepton support: {count} strict transitive checks passed"
