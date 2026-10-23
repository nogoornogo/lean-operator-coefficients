import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.Selection.ComposableBLSupport
import Physics.StandardModel.Operators.Dipole.ComposableDipoleSelection

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Composable selection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.ComposableBLSupport.union_forbidden_iff,
    ``Physics.ComposableBLSupport.all_union_forbidden_iff,
    ``Physics.ComposableBLSupport.fermionCharge,
    ``Physics.ComposableBLSupport.bosonCharge,
    ``Physics.ComposableBLSupport.specification,
    ``Physics.ComposableBLSupport.bOneTwo,
    ``Physics.ComposableBLSupport.bOneOrLTwo,
    ``Physics.ComposableBLSupport.charge_eq,
    ``Physics.ComposableBLSupport.old_support,
    ``Physics.ComposableBLSupport.bOne_or_lTwo,
    ``Physics.ComposableBLSupport.bOne_or_bTwo,
    ``Physics.ComposableBLSupport.inputEquiv,
    ``Physics.ComposableBLSupport.equiv,
    ``Physics.ComposableBLSupport.reconstruct_extract,
    ``Physics.ComposableBLSupport.extract_reconstruct,
    ``Physics.ComposableBLSupport.forbidden,
    ``Physics.ComposableDipoleSelection.residual,
    ``Physics.ComposableDipoleSelection.selector,
    ``Physics.ComposableDipoleSelection.extraction,
    ``Physics.ComposableDipoleSelection.forbidden_iff,
    ``Physics.ComposableDipoleSelection.forbidden_of_weights]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Composable selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Composable selection: {ds.length} strict transitive checks passed"
