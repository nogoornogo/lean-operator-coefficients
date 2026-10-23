import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraCoefficientReevaluation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraCoefficientReevaluation imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraCoefficientReevaluation.projectedAction,
    ``Physics.DevMohapatraCoefficientReevaluation.projectedAction_coefficient,
    ``Physics.DevMohapatraCoefficientReevaluation.independent_comparison,
    ``Physics.DevMohapatraCoefficientReevaluation.ordered_comparison]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraCoefficientReevaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraCoefficientReevaluation: {ds.length} strict transitive checks passed"
