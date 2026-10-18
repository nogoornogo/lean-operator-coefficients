import Physics.StandardModel.Operators.DevMohapatraHeavyElimination
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyElimination imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraHeavyElimination.V,
    ``GUT.DevMohapatraHeavyElimination.R,
    ``GUT.DevMohapatraHeavyElimination.coord,
    ``GUT.DevMohapatraHeavyElimination.u,
    ``GUT.DevMohapatraHeavyElimination.d,
    ``GUT.DevMohapatraHeavyElimination.s,
    ``GUT.DevMohapatraHeavyElimination.ub,
    ``GUT.DevMohapatraHeavyElimination.db,
    ``GUT.DevMohapatraHeavyElimination.sb,
    ``GUT.DevMohapatraHeavyElimination.cross,
    ``GUT.DevMohapatraHeavyElimination.cross_degree,
    ``GUT.DevMohapatraHeavyElimination.kernel,
    ``GUT.DevMohapatraHeavyElimination.kernel_degree,
    ``GUT.DevMohapatraHeavyElimination.kernel_nilpotent,
    ``GUT.DevMohapatraHeavyElimination.source,
    ``GUT.DevMohapatraHeavyElimination.solution,
    ``GUT.DevMohapatraHeavyElimination.source_equation,
    ``GUT.DevMohapatraHeavyElimination.source_unique,
    ``GUT.DevMohapatraHeavyElimination.cross_commutes,
    ``GUT.DevMohapatraHeavyElimination.residual,
    ``GUT.DevMohapatraHeavyElimination.residual_factor,
    ``GUT.DevMohapatraHeavyElimination.stationary,
    ``GUT.DevMohapatraHeavyElimination.stationary_unique,
    ``GUT.DevMohapatraHeavyElimination.cross_even,
    ``GUT.DevMohapatraHeavyElimination.kernel_even,
    ``GUT.DevMohapatraHeavyElimination.current_odd,
    ``GUT.DevMohapatraHeavyElimination.source_odd,
    ``GUT.DevMohapatraHeavyElimination.kernel_preserves_odd,
    ``GUT.DevMohapatraHeavyElimination.solution_odd,
    ``GUT.DevMohapatraHeavyElimination.quadratic,
    ``GUT.DevMohapatraHeavyElimination.linear,
    ``GUT.DevMohapatraHeavyElimination.constant,
    ``GUT.DevMohapatraHeavyElimination.action,
    ``GUT.DevMohapatraHeavyElimination.euler,
    ``GUT.DevMohapatraHeavyElimination.eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyElimination: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyElimination: {ds.length} strict transitive checks passed"
