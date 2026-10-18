import Physics.StandardModel.Operators.SMMinimumOperatorDimensionExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`GUT.SMMinimumOperatorDimension, `GUT.SMMinimumOperatorDimensionExamples]
  for required in [``GUT.SMMinimumOperatorDimension.c1_minimum,
      ``GUT.SMMinimumOperatorDimension.c2_minimum,
      ``GUT.SMMinimumOperatorDimension.h1_minimum,
      ``GUT.SMMinimumOperatorDimension.h2_minimum] do
    unless env.contains required do
      throwError "missing exact minimum {required}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) then
      for ax in (← Lean.collectAxioms name) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "operator dimension minimum {name} uses unexpected axiom {ax}"
      count := count+1
  if count < 35 then
    throwError "operator dimension minimum audit found only {count} declarations"
  Lean.logInfo m!"operator dimension minima: {count} strict transitive checks passed"
