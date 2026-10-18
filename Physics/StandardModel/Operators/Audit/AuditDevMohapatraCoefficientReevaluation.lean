import Physics.StandardModel.Operators.DevMohapatraCoefficientReevaluation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraCoefficientReevaluation imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraCoefficientReevaluation.projectedAction,
    ``GUT.DevMohapatraCoefficientReevaluation.projectedAction_coefficient,
    ``GUT.DevMohapatraCoefficientReevaluation.independent_comparison,
    ``GUT.DevMohapatraCoefficientReevaluation.ordered_comparison]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraCoefficientReevaluation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraCoefficientReevaluation: {ds.length} strict transitive checks passed"
