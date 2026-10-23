import Physics.StandardModel.Operators.Support.Dimension.SMMinimumOperatorDimensionExamples
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let prefixes := [`Physics.SMMinimumOperatorDimension, `Physics.SMMinimumOperatorDimensionExamples]
  for required in [``Physics.SMMinimumOperatorDimension.c1_minimum,
      ``Physics.SMMinimumOperatorDimension.c2_minimum,
      ``Physics.SMMinimumOperatorDimension.h1_minimum,
      ``Physics.SMMinimumOperatorDimension.h2_minimum] do
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
