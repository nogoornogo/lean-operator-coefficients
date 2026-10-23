import Math.Audit.ImportOrigin
import Math.Algebra.Variational.JetFirstVariation
import Math.Algebra.Variational.ConnectionFirstVariation

/-! Explicit public inventory; strict transitive standard-axiom and source-layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.JetFirstVariation.Poly,
    ``Math.JetFirstVariation.D,
    ``Math.JetFirstVariation.derivative_iterate,
    ``Math.JetFirstVariation.prolong,
    ``Math.JetFirstVariation.prolong_zero,
    ``Math.JetFirstVariation.prolong_shift,
    ``Math.JetFirstVariation.variation,
    ``Math.JetFirstVariation.variation_X,
    ``Math.JetFirstVariation.variation_field,
    ``Math.JetFirstVariation.variation_derivative,
    ``Math.JetFirstVariation.substitution,
    ``Math.JetFirstVariation.substitution_X,
    ``Math.JetFirstVariation.substitution_zero,
    ``Math.JetFirstVariation.substitution_first,
    ``Math.FormalConnection.curvature_variation,
    ``Math.MatrixFirstVariation.matrixVariation,
    ``Math.MatrixFirstVariation.eta,
    ``Math.MatrixFirstVariation.P,
    ``Math.MatrixFirstVariation.F,
    ``Math.MatrixFirstVariation.T,
    ``Math.MatrixFirstVariation.matrixVariation_mul,
    ``Math.MatrixFirstVariation.matrixVariation_commute,
    ``Math.MatrixFirstVariation.variation_trace,
    ``Math.MatrixFirstVariation.variation_curvature,
    ``Math.MatrixFirstVariation.variation_density,
    ``Math.MatrixFirstVariation.contraction,
    ``Math.MatrixFirstVariation.boundary,
    ``Math.MatrixFirstVariation.bulk,
    ``Math.MatrixFirstVariation.lagrangian,
    ``Math.MatrixFirstVariation.variation_smul,
    ``Math.MatrixFirstVariation.ordinary_smul,
    ``Math.MatrixFirstVariation.swapped_sum,
    ``Math.MatrixFirstVariation.variation_contraction,
    ``Math.MatrixFirstVariation.bulk_expansion,
    ``Math.MatrixFirstVariation.boundary_expansion,
    ``Math.MatrixFirstVariation.first_variation]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"First variation: {ds.length} strict transitive checks passed"
