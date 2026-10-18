import Physics.StandardModel.Spectrum.DualIndexAmbiguity
open Lean in
run_cmd do
  let ds := [
    ``GUT.SMDualIndexAmbiguity.equal_dual_index,
    ``GUT.SMDualIndexAmbiguity.generation_character_one,
    ``GUT.SMDualIndexAmbiguity.enlarged_character_one,
    ``GUT.SMDualIndexAmbiguity.not_equiv]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dual index {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dual index: {ds.length} strict transitive checks passed"
