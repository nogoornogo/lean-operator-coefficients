import Physics.StandardModel.Operators.DevMohapatraExternalLeg
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "External-leg adapter imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraExternalLeg.massKernel,
    ``GUT.DevMohapatraExternalLeg.massInverse,
    ``GUT.DevMohapatraExternalLeg.inverse_left,
    ``GUT.DevMohapatraExternalLeg.inverse_right,
    ``GUT.DevMohapatraExternalLeg.mass_action,
    ``GUT.DevMohapatraExternalLeg.source,
    ``GUT.DevMohapatraExternalLeg.sewn,
    ``GUT.DevMohapatraExternalLeg.sewn_current,
    ``GUT.DevMohapatraExternalLeg.sewn_generated,
    ``GUT.DevMohapatraExternalLeg.sewn_uv,
    ``GUT.DevMohapatraExternalLeg.fixed_leg,
    ``GUT.DevMohapatraExternalLeg.completedAction,
    ``GUT.DevMohapatraExternalLeg.completion_projection_free,
    ``GUT.DevMohapatraExternalLeg.completion_projection]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "External-leg adapter: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"External-leg adapter: {ds.length} strict transitive checks passed"
