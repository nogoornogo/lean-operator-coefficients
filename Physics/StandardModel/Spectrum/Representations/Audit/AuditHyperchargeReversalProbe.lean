import Physics.StandardModel.Spectrum.Representations.HyperchargeReversalProbe
open Lean in
run_cmd do
  let ds := [``Physics.HyperchargeReversalProbe.character_of_hypercharge,
    ``Physics.HyperchargeReversalProbe.generation_character,
    ``Physics.HyperchargeReversalProbe.generation_probe_nonzero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM reversal probe {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM reversal probe: {ds.length} strict transitive checks passed"
