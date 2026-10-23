import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraNormalizationClosure
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraNormalizationClosure imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraNormalizationClosure.coordinates,
    ``Physics.DevMohapatraNormalizationClosure.coordinates_fields,
    ``Physics.DevMohapatraNormalizationClosure.operator_nonzero,
    ``Physics.DevMohapatraNormalizationClosure.paper_nonzero,
    ``Physics.DevMohapatraNormalizationClosure.action_ne_paper,
    ``Physics.DevMohapatraNormalizationClosure.ordered_action_ne_paper,
    ``Physics.DevMohapatraNormalizationClosure.normalization_coefficient,
    ``Physics.DevMohapatraNormalizationClosure.normalization_match_iff,
    ``Physics.DevMohapatraNormalizationClosure.consistent_bilinear_match_iff]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraNormalizationClosure: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraNormalizationClosure: {ds.length} strict transitive checks passed"
