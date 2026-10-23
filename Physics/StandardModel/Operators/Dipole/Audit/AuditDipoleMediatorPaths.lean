import Physics.StandardModel.Operators.Dipole.DipoleMediatorControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dipole mediator paths import model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.WeightedSelectedPaths.selected,
    ``Math.WeightedSelectedPaths.nonzero_iff,
    ``Math.WeightedSelectedPaths.selected_isolated,
    ``Math.WeightedSelectedPaths.exists_nonzero_iff_path,
    ``Math.WeightedSelectedPaths.nonzero_of_single_selected_path,
    ``Math.WeightedSelectedPaths.squares_isolate,
    ``Math.WeightedSelectedPaths.cancellation,
    ``Math.WeightedSelectedPaths.cancellation_paths_nonzero,
    ``Physics.DipoleMediatorPaths.path_selected,
    ``Physics.DipoleMediatorPaths.selected,
    ``Physics.DipoleMediatorPaths.nonzero_iff,
    ``Physics.DipoleMediatorPaths.exists_nonzero_iff_path,
    ``Physics.DipoleMediatorPaths.nonzero_of_single_selected_path,
    ``Physics.DipoleMediatorPaths.nonzero_of_mediator_witness,
    ``Physics.DipoleMediatorPaths.selected_of_factorization,
    ``Physics.DipoleMediatorPaths.realized_iff_path_of_factorization,
    ``Physics.DipoleMediatorControls.weights_isolate,
    ``Physics.DipoleMediatorControls.selected,
    ``Physics.DipoleMediatorControls.nonzero_iff,
    ``Physics.DipoleMediatorControls.each_path_nonzero,
    ``Physics.DipoleMediatorControls.cancellation,
    ``Physics.DipoleMediatorControls.restricted_family_vanishes,
    ``Physics.DipoleMediatorControls.realized]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dipole mediator paths: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dipole mediator paths: {declarations.length} strict transitive axiom checks passed"
