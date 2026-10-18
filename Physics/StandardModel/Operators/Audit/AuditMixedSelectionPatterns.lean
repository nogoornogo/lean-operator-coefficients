import Physics.StandardModel.Operators.MixedSelectionPatterns
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Mixed selection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.MixedSelectionPatterns.BgwTarget,
    ``GUT.MixedSelectionPatterns.bgwDomain,
    ``GUT.MixedSelectionPatterns.bgwRequest,
    ``GUT.MixedSelectionPatterns.bgw_domain_forbidden_iff,
    ``GUT.MixedSelectionPatterns.bgw_satisfies,
    ``GUT.MixedSelectionPatterns.bgw_components,
    ``GUT.MixedSelectionPatterns.dgt_selected_allowed,
    ``GUT.MixedSelectionPatterns.dgt_selector_range_allowed]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed selection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed selection: {ds.length} strict transitive checks passed"
