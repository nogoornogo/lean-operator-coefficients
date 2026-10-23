import Physics.StandardModel.Operators.Support.Dimension.SMB1MinimumClassificationExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`Physics.SMB1DimensionBounds, `Physics.SMB1DimensionProposals,
    `Physics.SMB1DimensionWitnesses, `Physics.SMB1MinimumClassification,
    `Physics.SMB1MinimumClassificationExamples]
  for required in [``Physics.SMB1DimensionBounds.original_grade_congruence,
      ``Physics.SMB1DimensionWitnesses.upper_attains,
      ``Physics.SMB1MinimumClassification.row_certificate,
      ``Physics.SMB1MinimumClassification.row_exact,
      ``Physics.SMB1MinimumClassification.interval_counts] do
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
