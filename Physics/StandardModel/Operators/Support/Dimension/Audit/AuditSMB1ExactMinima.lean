import Physics.StandardModel.Operators.Support.Dimension.SMB1ExactMinimaExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`Physics.SMB1WeakCountArithmetic, `Physics.SMB1WeakDimensionBounds,
    `Physics.SMB1StrongDimensionBounds, `Physics.SMB1ExactMinima, `Physics.SMB1ExactMinimaExamples]
  for required in [``Physics.SMB1WeakCountArithmetic.weak_envelope,
      ``Physics.SMB1WeakDimensionBounds.original_weak_envelope,
      ``Physics.SMB1StrongDimensionBounds.original_lower,
      ``Physics.SMB1ExactMinima.row_minimum,
      ``Physics.SMB1ExactMinima.none_iff_forbidden,
      ``Physics.SMB1ExactMinima.minimum_distribution] do
    unless env.contains required do
      throwError "missing exact B1 minimum interface {required}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "exact B1 minimum {name} uses unexpected axiom {ax}"
      count := count+1
  if count < 30 then
    throwError "exact B1 minimum audit found only {count} declarations"
  Lean.logInfo m!"exact B1 minima: {count} strict transitive checks passed"
