import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHeavyProjection
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyProjection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``Physics.DevMohapatraHeavyProjection.Light,
    ``Physics.DevMohapatraHeavyProjection.holomorphicFields,
    ``Physics.DevMohapatraHeavyProjection.project,
    ``Physics.DevMohapatraHeavyProjection.ul,
    ``Physics.DevMohapatraHeavyProjection.dl,
    ``Physics.DevMohapatraHeavyProjection.sl,
    ``Physics.DevMohapatraHeavyProjection.holomorphicFields_bar,
    ``Physics.DevMohapatraHeavyProjection.project_current,
    ``Physics.DevMohapatraHeavyProjection.project_bar_current,
    ``Physics.DevMohapatraHeavyProjection.project_cross,
    ``Physics.DevMohapatraHeavyProjection.project_kernel,
    ``Physics.DevMohapatraHeavyProjection.project_solution_source,
    ``Physics.DevMohapatraHeavyProjection.project_bar_solution,
    ``Physics.DevMohapatraHeavyProjection.project_constant,
    ``Physics.DevMohapatraHeavyProjection.project_eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyProjection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyProjection: {ds.length} strict transitive checks passed"
