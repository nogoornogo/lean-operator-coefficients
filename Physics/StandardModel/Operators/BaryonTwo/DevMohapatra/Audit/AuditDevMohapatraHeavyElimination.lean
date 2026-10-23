import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyElimination
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyElimination imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraHeavyElimination.V,
    ``Physics.DevMohapatraHeavyElimination.R,
    ``Physics.DevMohapatraHeavyElimination.coord,
    ``Physics.DevMohapatraHeavyElimination.u,
    ``Physics.DevMohapatraHeavyElimination.d,
    ``Physics.DevMohapatraHeavyElimination.s,
    ``Physics.DevMohapatraHeavyElimination.ub,
    ``Physics.DevMohapatraHeavyElimination.db,
    ``Physics.DevMohapatraHeavyElimination.sb,
    ``Physics.DevMohapatraHeavyElimination.cross,
    ``Physics.DevMohapatraHeavyElimination.cross_degree,
    ``Physics.DevMohapatraHeavyElimination.kernel,
    ``Physics.DevMohapatraHeavyElimination.kernel_degree,
    ``Physics.DevMohapatraHeavyElimination.kernel_nilpotent,
    ``Physics.DevMohapatraHeavyElimination.source,
    ``Physics.DevMohapatraHeavyElimination.solution,
    ``Physics.DevMohapatraHeavyElimination.source_equation,
    ``Physics.DevMohapatraHeavyElimination.source_unique,
    ``Physics.DevMohapatraHeavyElimination.cross_commutes,
    ``Physics.DevMohapatraHeavyElimination.residual,
    ``Physics.DevMohapatraHeavyElimination.residual_factor,
    ``Physics.DevMohapatraHeavyElimination.stationary,
    ``Physics.DevMohapatraHeavyElimination.stationary_unique,
    ``Physics.DevMohapatraHeavyElimination.cross_even,
    ``Physics.DevMohapatraHeavyElimination.kernel_even,
    ``Physics.DevMohapatraHeavyElimination.current_odd,
    ``Physics.DevMohapatraHeavyElimination.source_odd,
    ``Physics.DevMohapatraHeavyElimination.kernel_preserves_odd,
    ``Physics.DevMohapatraHeavyElimination.solution_odd,
    ``Physics.DevMohapatraHeavyElimination.quadratic,
    ``Physics.DevMohapatraHeavyElimination.linear,
    ``Physics.DevMohapatraHeavyElimination.constant,
    ``Physics.DevMohapatraHeavyElimination.action,
    ``Physics.DevMohapatraHeavyElimination.euler,
    ``Physics.DevMohapatraHeavyElimination.eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyElimination: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyElimination: {ds.length} strict transitive checks passed"
