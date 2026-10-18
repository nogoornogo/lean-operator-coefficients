import Physics.StandardModel.Operators.DevMohapatraNormalizationClosure
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraNormalizationClosure imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraNormalizationClosure.coordinates,
    ``GUT.DevMohapatraNormalizationClosure.coordinates_fields,
    ``GUT.DevMohapatraNormalizationClosure.operator_nonzero,
    ``GUT.DevMohapatraNormalizationClosure.paper_nonzero,
    ``GUT.DevMohapatraNormalizationClosure.action_ne_paper,
    ``GUT.DevMohapatraNormalizationClosure.ordered_action_ne_paper,
    ``GUT.DevMohapatraNormalizationClosure.normalization_coefficient,
    ``GUT.DevMohapatraNormalizationClosure.normalization_match_iff,
    ``GUT.DevMohapatraNormalizationClosure.consistent_bilinear_match_iff]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraNormalizationClosure: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraNormalizationClosure: {ds.length} strict transitive checks passed"
