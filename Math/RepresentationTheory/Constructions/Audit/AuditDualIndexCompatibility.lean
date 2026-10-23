import Math.RepresentationTheory.Constructions.DualIndexCompatibility
open Lean in
run_cmd do
  let ds := [
    ``Math.DualIndexCompatibility.withSinglet_dual_index,
    ``Math.DualIndexCompatibility.withSinglet_character_ne,
    ``Math.DualIndexCompatibility.withSinglet_not_equiv,
    ``Math.DualIndexCompatibility.withVectorlike_dual_index,
    ``Math.DualIndexCompatibility.dual_index_invariant]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dual index {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dual index: {ds.length} strict transitive checks passed"
