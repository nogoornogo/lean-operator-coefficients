import Math.RepresentationTheory.PointwiseGaugeRemoval
open Lean in
run_cmd do
  let ds := [
    ``Math.PointwiseGaugeRemoval.projection_local,
    ``Math.PointwiseGaugeRemoval.removed_projection,
    ``Math.PointwiseGaugeRemoval.removed_mul_projection,
    ``Math.PointwiseGaugeRemoval.invariant_removed,
    ``Math.PointwiseGaugeRemoval.removed_commutes,
    ``Math.PointwiseGaugeRemoval.quotient_eq,
    ``Math.PointwiseGaugeRemoval.invariantEquiv,
    ``Math.PointwiseGaugeRemoval.forbidden_iff,
    ``Math.PointwiseGaugeRemoval.nonzero_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Gauge comparison {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Gauge comparison: {ds.length} strict transitive checks passed"
