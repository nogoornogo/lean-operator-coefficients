import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraExternalLeg
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "External-leg adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraExternalLeg.massKernel,
    ``Physics.DevMohapatraExternalLeg.massInverse,
    ``Physics.DevMohapatraExternalLeg.inverse_left,
    ``Physics.DevMohapatraExternalLeg.inverse_right,
    ``Physics.DevMohapatraExternalLeg.mass_action,
    ``Physics.DevMohapatraExternalLeg.source,
    ``Physics.DevMohapatraExternalLeg.sewn,
    ``Physics.DevMohapatraExternalLeg.sewn_current,
    ``Physics.DevMohapatraExternalLeg.sewn_generated,
    ``Physics.DevMohapatraExternalLeg.sewn_uv,
    ``Physics.DevMohapatraExternalLeg.fixed_leg,
    ``Physics.DevMohapatraExternalLeg.completedAction,
    ``Physics.DevMohapatraExternalLeg.completion_projection_free,
    ``Physics.DevMohapatraExternalLeg.completion_projection]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "External-leg adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"External-leg adapter: {ds.length} strict transitive checks passed"
