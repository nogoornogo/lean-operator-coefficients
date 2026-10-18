import Physics.StandardModel.Operators.DevMohapatraHeavyAction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyAction imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraHeavyAction.W,
    ``GUT.DevMohapatraHeavyAction.B,
    ``GUT.DevMohapatraHeavyAction.includeExternal,
    ``GUT.DevMohapatraHeavyAction.heavyVector,
    ``GUT.DevMohapatraHeavyAction.heavy,
    ``GUT.DevMohapatraHeavyAction.dual,
    ``GUT.DevMohapatraHeavyAction.derivative,
    ``GUT.DevMohapatraHeavyAction.derivative_mul,
    ``GUT.DevMohapatraHeavyAction.derivative_external,
    ``GUT.DevMohapatraHeavyAction.derivative_heavy,
    ``GUT.DevMohapatraHeavyAction.heavy_odd,
    ``GUT.DevMohapatraHeavyAction.universalAction,
    ``GUT.DevMohapatraHeavyAction.evalLinear,
    ``GUT.DevMohapatraHeavyAction.evalLinear_odd,
    ``GUT.DevMohapatraHeavyAction.evaluate,
    ``GUT.DevMohapatraHeavyAction.evaluate_external,
    ``GUT.DevMohapatraHeavyAction.evaluate_heavy,
    ``GUT.DevMohapatraHeavyAction.differentiated_action,
    ``GUT.DevMohapatraHeavyAction.stationary,
    ``GUT.DevMohapatraHeavyAction.stationary_unique,
    ``GUT.DevMohapatraHeavyAction.evaluated_action,
    ``GUT.DevMohapatraHeavyAction.eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyAction: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyAction: {ds.length} strict transitive checks passed"
