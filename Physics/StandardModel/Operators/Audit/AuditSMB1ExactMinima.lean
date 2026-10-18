import Physics.StandardModel.Operators.SMB1ExactMinimaExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`GUT.SMB1WeakCountArithmetic, `GUT.SMB1WeakDimensionBounds,
    `GUT.SMB1StrongDimensionBounds, `GUT.SMB1ExactMinima, `GUT.SMB1ExactMinimaExamples]
  for required in [``GUT.SMB1WeakCountArithmetic.weak_envelope,
      ``GUT.SMB1WeakDimensionBounds.original_weak_envelope,
      ``GUT.SMB1StrongDimensionBounds.original_lower,
      ``GUT.SMB1ExactMinima.row_minimum,
      ``GUT.SMB1ExactMinima.none_iff_forbidden,
      ``GUT.SMB1ExactMinima.minimum_distribution] do
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
