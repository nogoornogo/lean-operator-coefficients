import Physics.StandardModel.Operators.SMB1MinimumClassificationExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`GUT.SMB1DimensionBounds, `GUT.SMB1DimensionProposals,
    `GUT.SMB1DimensionWitnesses, `GUT.SMB1MinimumClassification,
    `GUT.SMB1MinimumClassificationExamples]
  for required in [``GUT.SMB1DimensionBounds.original_grade_congruence,
      ``GUT.SMB1DimensionWitnesses.upper_attains,
      ``GUT.SMB1MinimumClassification.row_certificate,
      ``GUT.SMB1MinimumClassification.row_exact,
      ``GUT.SMB1MinimumClassification.interval_counts] do
    unless env.contains required do
      throwError "missing retained B1 dimension interface {required}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "retained B1 dimensions {name} uses unexpected axiom {ax}"
      count := count+1
  if count < 75 then
    throwError "retained B1 dimension audit found only {count} declarations"
  Lean.logInfo m!"retained B1 dimensions: {count} strict transitive checks passed"
