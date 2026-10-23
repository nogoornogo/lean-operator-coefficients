import Math.RepresentationTheory.Invariants.CovariantCharacterObstruction
open Lean in
run_cmd do
  let ds := [``Math.CovariantCharacterObstruction.character_invariant,
    ``Math.CovariantCharacterObstruction.dual_index_zero_of_inverse,
    ``Math.CovariantCharacterObstruction.dual_index_zero_of_conjugate_inverse]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Covariant character {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Covariant character: {ds.length} strict transitive checks passed"
