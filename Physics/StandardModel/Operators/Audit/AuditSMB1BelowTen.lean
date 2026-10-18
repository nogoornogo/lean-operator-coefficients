import Physics.StandardModel.Operators.SMB1BelowTenExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`GUT.SMB1BelowTen, `GUT.SMB1BelowTenAssignments, `GUT.SMB1BelowTenExamples]
  for required in [``GUT.SMB1BelowTen.allowed_iff,
      ``GUT.SMB1BelowTen.forbidden_iff,
      ``GUT.SMB1BelowTenAssignments.row_decision,
      ``GUT.SMB1BelowTenAssignments.counts,
      ``GUT.SMB1BelowTenAssignments.coverage] do
    unless env.contains required do
      throwError "missing B1 bounded classification {required}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "B1 bounded classification {name} uses unexpected axiom {ax}"
      count := count+1
  if count < 30 then
    throwError "B1 bounded classification audit found only {count} declarations"
  Lean.logInfo m!"B1 below ten: {count} strict transitive checks passed"
