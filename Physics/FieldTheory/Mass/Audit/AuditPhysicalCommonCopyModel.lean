import Physics.FieldTheory.Mass.PhysicalCommonCopyModel
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected model-layer dependency: {mod}"
    let origin := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf origin || (`GUT.SU6).isPrefixOf origin then
      throwError "Unexpected original SU5/SU6 dependency: {mod}"
  let declarations := [
    ``GUT.PhysicalCommonCopyModel.externalMap,
    ``GUT.PhysicalCommonCopyModel.Species.lightEmbedding,
    ``GUT.PhysicalCommonCopyModel.Species.light_injective,
    ``GUT.PhysicalCommonCopyModel.Species.light_mem_radical,
    ``GUT.PhysicalCommonCopyModel.Species.rangeCoords,
    ``GUT.PhysicalCommonCopyModel.Species.rangeRho,
    ``GUT.PhysicalCommonCopyModel.Species.range_action,
    ``GUT.PhysicalCommonCopyModel.Species.range_light,
    ``GUT.PhysicalCommonCopyModel.speciesOfDirac,
    ``GUT.PhysicalCommonCopyModel.dualExternalEquiv,
    ``GUT.PhysicalCommonCopyModel.Realization.quarkEq,
    ``GUT.PhysicalCommonCopyModel.Realization.upEq,
    ``GUT.PhysicalCommonCopyModel.Realization.electronEq,
    ``GUT.PhysicalCommonCopyModel.Realization.HasLightExterior,
    ``GUT.PhysicalCommonCopyModel.Realization.light_exterior,
    ``GUT.PhysicalCommonCopyModel.Model.arbitrary_mass_light_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"PhysicalCommonCopyModel: {declarations.length} strict transitive axiom checks; no model-layer or original SU5/SU6 imports"
