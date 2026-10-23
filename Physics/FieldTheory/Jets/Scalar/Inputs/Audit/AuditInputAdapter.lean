import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarInputAdapter
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarDerivativeInterface

/-! Explicit public declaration inventory with strict transitive axiom/layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.ScalarInputAdapter.action,
    ``Physics.ScalarInputAdapter.stable,
    ``Physics.ScalarInputAdapter.Input,
    ``Physics.ScalarInputAdapter.equiv,
    ``Physics.ScalarInputAdapter.admissible_iff,
    ``Physics.ScalarInputAdapter.extraction,
    ``Physics.ScalarInputAdapter.reconstruction,
    ``Physics.ScalarInputAdapter.interaction_constraint,
    ``Physics.ScalarInputAdapter.nonzero_iff,
    ``Physics.ScalarInputAdapter.lorentzAction,
    ``Physics.ScalarInputAdapter.lorentz_stable,
    ``Physics.ScalarInputAdapter.LorentzInput,
    ``Physics.ScalarInputAdapter.lorentzEquiv,
    ``Physics.ScalarInputAdapter.lorentz_extraction,
    ``Physics.ScalarInputAdapter.lorentz_interaction_constraint,
    ``Physics.ScalarDerivativeInterface.scalar,
    ``Physics.ScalarDerivativeInterface.compatibleInput,
    ``Physics.ScalarDerivativeInterface.compatible_map,
    ``Physics.ScalarDerivativeInterface.scalar_extraction,
    ``Physics.ScalarDerivativeInterface.interactionSource,
    ``Physics.ScalarDerivativeInterface.wave_mem,
    ``Physics.ScalarDerivativeInterface.cubic_mem,
    ``Physics.ScalarDerivativeInterface.interaction_stable,
    ``Physics.ScalarDerivativeInterface.selected,
    ``Physics.ScalarDerivativeInterface.wave,
    ``Physics.ScalarDerivativeInterface.cubic,
    ``Physics.ScalarDerivativeInterface.seed_mem_source,
    ``Physics.ScalarDerivativeInterface.selectedSeed,
    ``Physics.ScalarDerivativeInterface.selected_seed_relation,
    ``Physics.ScalarDerivativeInterface.selected_interaction,
    ``Physics.ScalarDerivativeInterface.selectedImageEquiv,
    ``Physics.ScalarDerivativeInterface.restriction_agrees]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Derivative input adapters: {ds.length} strict transitive checks passed"
