import Math.LinearAlgebra.Constructions.FourSlotGeneration
import Lean.Util.CollectAxioms

run_cmd do
  for ax in (← Lean.collectAxioms ``Math.FourSlotGeneration.ext) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Four-slot generation uses unexpected axiom {ax}"
  Lean.logInfo "Four-slot generation: 1 strict axiom check passed"
