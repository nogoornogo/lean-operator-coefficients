import Math.LinearAlgebra.Selection.MixedSelectionRequests
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Mixed selection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Math.MixedSelectionRequests.Request,
    ``Math.MixedSelectionRequests.Satisfies,
    ``Math.MixedSelectionRequests.combine,
    ``Math.MixedSelectionRequests.forbidden,
    ``Math.MixedSelectionRequests.allowed,
    ``Math.MixedSelectionRequests.combine_iff,
    ``Math.MixedSelectionRequests.conflict,
    ``Math.MixedSelectionRequests.empty_satisfied,
    ``Math.MixedSelectionRequests.SelectedAllowed,
    ``Math.MixedSelectionRequests.selected_allowed_iff_range,
    ``Math.MixedSelectionRequests.selector_zero_iff_not_allowed,
    ``Math.MixedSelectionRequests.range_forbidden_iff,
    ``Math.MixedSelectionRequests.whole_domain_not_selected,
    ``Math.MixedSelectionRequests.transport]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed selection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed selection: {ds.length} strict transitive checks passed"
