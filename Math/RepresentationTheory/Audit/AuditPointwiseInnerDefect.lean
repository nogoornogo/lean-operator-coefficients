import Math.RepresentationTheory.PointwiseInnerDefect
open Lean in
run_cmd do
  let ds := [
    ``Math.PointwiseInnerDefect.removed_mul,
    ``Math.PointwiseInnerDefect.removed_mul_iff,
    ``Math.PointwiseInnerDefect.removedRepresentation,
    ``Math.PointwiseInnerDefect.removedRepresentation_commutes]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Inner defect {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Inner defect: {ds.length} strict transitive checks passed"
