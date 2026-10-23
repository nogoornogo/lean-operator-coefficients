import Physics.StandardModel.Operators.Selection.MixedSelectionPatterns
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Mixed selection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.MixedSelectionPatterns.BgwTarget,
    ``Physics.MixedSelectionPatterns.bgwDomain,
    ``Physics.MixedSelectionPatterns.bgwRequest,
    ``Physics.MixedSelectionPatterns.bgw_domain_forbidden_iff,
    ``Physics.MixedSelectionPatterns.bgw_satisfies,
    ``Physics.MixedSelectionPatterns.bgw_components,
    ``Physics.MixedSelectionPatterns.dgt_selected_allowed,
    ``Physics.MixedSelectionPatterns.dgt_selector_range_allowed]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed selection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed selection: {ds.length} strict transitive checks passed"
