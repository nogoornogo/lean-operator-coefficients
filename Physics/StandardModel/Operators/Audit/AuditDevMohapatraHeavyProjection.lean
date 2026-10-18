import Physics.StandardModel.Operators.DevMohapatraHeavyProjection
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "DevMohapatraHeavyProjection imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.DevMohapatraHeavyProjection.Light,
    ``GUT.DevMohapatraHeavyProjection.holomorphicFields,
    ``GUT.DevMohapatraHeavyProjection.project,
    ``GUT.DevMohapatraHeavyProjection.ul,
    ``GUT.DevMohapatraHeavyProjection.dl,
    ``GUT.DevMohapatraHeavyProjection.sl,
    ``GUT.DevMohapatraHeavyProjection.holomorphicFields_bar,
    ``GUT.DevMohapatraHeavyProjection.project_current,
    ``GUT.DevMohapatraHeavyProjection.project_bar_current,
    ``GUT.DevMohapatraHeavyProjection.project_cross,
    ``GUT.DevMohapatraHeavyProjection.project_kernel,
    ``GUT.DevMohapatraHeavyProjection.project_solution_source,
    ``GUT.DevMohapatraHeavyProjection.project_bar_solution,
    ``GUT.DevMohapatraHeavyProjection.project_constant,
    ``GUT.DevMohapatraHeavyProjection.project_eliminated_action]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "DevMohapatraHeavyProjection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"DevMohapatraHeavyProjection: {ds.length} strict transitive checks passed"
