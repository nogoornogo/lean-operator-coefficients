import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyAction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyAction imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraHeavyAction.W,
    ``Physics.DevMohapatraHeavyAction.B,
    ``Physics.DevMohapatraHeavyAction.includeExternal,
    ``Physics.DevMohapatraHeavyAction.heavyVector,
    ``Physics.DevMohapatraHeavyAction.heavy,
    ``Physics.DevMohapatraHeavyAction.dual,
    ``Physics.DevMohapatraHeavyAction.derivative,
    ``Physics.DevMohapatraHeavyAction.derivative_mul,
    ``Physics.DevMohapatraHeavyAction.derivative_external,
    ``Physics.DevMohapatraHeavyAction.derivative_heavy,
    ``Physics.DevMohapatraHeavyAction.heavy_odd,
    ``Physics.DevMohapatraHeavyAction.universalAction,
    ``Physics.DevMohapatraHeavyAction.evalLinear,
    ``Physics.DevMohapatraHeavyAction.evalLinear_odd,
    ``Physics.DevMohapatraHeavyAction.evaluate,
    ``Physics.DevMohapatraHeavyAction.evaluate_external,
    ``Physics.DevMohapatraHeavyAction.evaluate_heavy,
    ``Physics.DevMohapatraHeavyAction.differentiated_action,
    ``Physics.DevMohapatraHeavyAction.stationary,
    ``Physics.DevMohapatraHeavyAction.stationary_unique,
    ``Physics.DevMohapatraHeavyAction.evaluated_action,
    ``Physics.DevMohapatraHeavyAction.eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyAction: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyAction: {ds.length} strict transitive checks passed"
