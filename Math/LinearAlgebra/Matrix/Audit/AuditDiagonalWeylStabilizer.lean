import Math.LinearAlgebra.Matrix.DiagonalWeylStabilizer
open Lean in
run_cmd do
  let ds := [``Math.DiagonalWeylStabilizer.permutation_conjugate, ``Math.DiagonalWeylStabilizer.representative_conjugate, ``Math.DiagonalWeylStabilizer.fixed_iff, ``Math.DiagonalWeylStabilizer.preserving, ``Math.DiagonalWeylStabilizer.fixed_iff_mem, ``Math.DiagonalWeylStabilizer.split_preserves_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Diagonal Weyl {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Diagonal Weyl: {ds.length} strict transitive checks passed"
