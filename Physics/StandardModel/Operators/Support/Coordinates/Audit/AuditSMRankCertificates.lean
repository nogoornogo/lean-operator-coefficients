import Physics.StandardModel.Operators.Support.Coordinates.SMRankMultiplicity
import Physics.StandardModel.Operators.Support.Coordinates.SMExactRankBridge
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM rank certificate audit imports {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.SMRankMultiplicity.actionEquiv,
    ``Physics.SMRankMultiplicity.kernelEquiv, ``Physics.SMRankMultiplicity.rank_eq,
    ``Physics.SMExactRankBridge.rank_from_certificate]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM rank certificate audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM rank certificate audit: layer and {ds.length} strict transitive checks passed"
