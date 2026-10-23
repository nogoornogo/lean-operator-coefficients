import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarFirstVariation
import Physics.FieldTheory.Jets.Gauge.YangMillsFirstVariation

/-! Explicit public inventory; strict transitive standard-axiom and source-layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.ScalarFirstVariation.delta,
    ``Physics.ScalarFirstVariation.lagrangian,
    ``Physics.ScalarFirstVariation.current,
    ``Physics.ScalarFirstVariation.delta_field,
    ``Physics.ScalarFirstVariation.delta_first,
    ``Physics.ScalarFirstVariation.first_variation,
    ``Physics.ScalarFirstVariation.first_variation_mod_ibp,
    ``Physics.ScalarFirstVariation.first_variation_onShell,
    ``Physics.ScalarFirstVariation.substitution_first,
    ``Physics.ScalarFirstVariation.eulerEquation,
    ``Physics.ScalarFirstVariation.euler_ideal_eq,
    ``Physics.YangMillsFirstVariation.delta,
    ``Physics.YangMillsFirstVariation.matrixDelta,
    ``Physics.YangMillsFirstVariation.delta_connection,
    ``Physics.YangMillsFirstVariation.delta_derivative,
    ``Physics.YangMillsFirstVariation.lagrangian,
    ``Physics.YangMillsFirstVariation.current,
    ``Physics.YangMillsFirstVariation.eomPairing,
    ``Physics.YangMillsFirstVariation.ordinary_bridge,
    ``Physics.YangMillsFirstVariation.curvature_variation,
    ``Physics.YangMillsFirstVariation.first_variation,
    ``Physics.YangMillsFirstVariation.eomPairing_mem,
    ``Physics.YangMillsFirstVariation.first_variation_mod_ibp,
    ``Physics.YangMillsFirstVariation.first_variation_onShell,
    ``Physics.YangMillsFirstVariation.substitution_first,
    ``Physics.YangMillsFirstVariation.componentVariation,
    ``Physics.YangMillsFirstVariation.component_pairing,
    ``Physics.YangMillsFirstVariation.component_eom_iff,
    ``Physics.YangMillsFirstVariation.component_first_variation_mod_ibp,
    ``Physics.YangMillsFirstVariation.eulerSeeds,
    ``Physics.YangMillsFirstVariation.euler_ideal_eq]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"First variation: {ds.length} strict transitive checks passed"
