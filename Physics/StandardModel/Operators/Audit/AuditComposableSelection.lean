import Math.Audit.ImportOrigin
import Physics.StandardModel.Operators.ComposableBLSupport
import Physics.StandardModel.Operators.ComposableDipoleSelection

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Composable selection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``GUT.ComposableBLSupport.union_forbidden_iff,
    ``GUT.ComposableBLSupport.all_union_forbidden_iff,
    ``GUT.ComposableBLSupport.fermionCharge,
    ``GUT.ComposableBLSupport.bosonCharge,
    ``GUT.ComposableBLSupport.specification,
    ``GUT.ComposableBLSupport.bOneTwo,
    ``GUT.ComposableBLSupport.bOneOrLTwo,
    ``GUT.ComposableBLSupport.charge_eq,
    ``GUT.ComposableBLSupport.old_support,
    ``GUT.ComposableBLSupport.bOne_or_lTwo,
    ``GUT.ComposableBLSupport.bOne_or_bTwo,
    ``GUT.ComposableBLSupport.inputEquiv,
    ``GUT.ComposableBLSupport.equiv,
    ``GUT.ComposableBLSupport.reconstruct_extract,
    ``GUT.ComposableBLSupport.extract_reconstruct,
    ``GUT.ComposableBLSupport.forbidden,
    ``GUT.ComposableDipoleSelection.residual,
    ``GUT.ComposableDipoleSelection.selector,
    ``GUT.ComposableDipoleSelection.extraction,
    ``GUT.ComposableDipoleSelection.forbidden_iff,
    ``GUT.ComposableDipoleSelection.forbidden_of_weights]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Composable selection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Composable selection: {ds.length} strict transitive checks passed"
