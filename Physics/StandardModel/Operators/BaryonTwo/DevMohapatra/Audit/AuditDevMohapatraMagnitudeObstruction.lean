import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraMagnitudeObstruction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraMagnitudeObstruction imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraMagnitudeObstruction.matching_norm,
    ``Physics.DevMohapatraMagnitudeObstruction.bounded_no_match,
    ``Physics.DevMohapatraMagnitudeObstruction.unit_phase_no_match,
    ``Physics.DevMohapatraMagnitudeObstruction.bounded_action_ne]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraMagnitudeObstruction: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraMagnitudeObstruction: {ds.length} strict transitive checks passed"
