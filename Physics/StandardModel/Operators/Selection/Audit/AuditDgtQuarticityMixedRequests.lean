import Physics.StandardModel.Operators.Selection.DgtQuarticityMixedRequests
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DGT/quarticity mixed imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DgtQuarticityMixedRequests.DgtTarget,
    ``Physics.DgtQuarticityMixedRequests.dgtDomain,
    ``Physics.DgtQuarticityMixedRequests.dgtRequest,
    ``Physics.DgtQuarticityMixedRequests.dgt_satisfies,
    ``Physics.DgtQuarticityMixedRequests.dgt_components,
    ``Physics.DgtQuarticityMixedRequests.dgt_uv_not_allowed,
    ``Physics.DgtQuarticityMixedRequests.QuarticityTarget,
    ``Physics.DgtQuarticityMixedRequests.quarticityDomain,
    ``Physics.DgtQuarticityMixedRequests.quarticityRequest,
    ``Physics.DgtQuarticityMixedRequests.quarticity_satisfies,
    ``Physics.DgtQuarticityMixedRequests.quarticity_components,
    ``Physics.DgtQuarticityMixedRequests.quarticity_dressed_not_forbidden,
    ``Physics.DgtQuarticityMixedRequests.forbidDressed,
    ``Physics.DgtQuarticityMixedRequests.quarticity_extended_request_inconsistent]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DGT/quarticity mixed: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DGT/quarticity mixed: {ds.length} strict transitive checks passed"
