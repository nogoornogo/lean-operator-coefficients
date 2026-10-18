import Physics.StandardModel.Operators.DgtQuarticityMixedRequests
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DGT/quarticity mixed imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DgtQuarticityMixedRequests.DgtTarget,
    ``GUT.DgtQuarticityMixedRequests.dgtDomain,
    ``GUT.DgtQuarticityMixedRequests.dgtRequest,
    ``GUT.DgtQuarticityMixedRequests.dgt_satisfies,
    ``GUT.DgtQuarticityMixedRequests.dgt_components,
    ``GUT.DgtQuarticityMixedRequests.dgt_uv_not_allowed,
    ``GUT.DgtQuarticityMixedRequests.QuarticityTarget,
    ``GUT.DgtQuarticityMixedRequests.quarticityDomain,
    ``GUT.DgtQuarticityMixedRequests.quarticityRequest,
    ``GUT.DgtQuarticityMixedRequests.quarticity_satisfies,
    ``GUT.DgtQuarticityMixedRequests.quarticity_components,
    ``GUT.DgtQuarticityMixedRequests.quarticity_dressed_not_forbidden,
    ``GUT.DgtQuarticityMixedRequests.forbidDressed,
    ``GUT.DgtQuarticityMixedRequests.quarticity_extended_request_inconsistent]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DGT/quarticity mixed: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DGT/quarticity mixed: {ds.length} strict transitive checks passed"
