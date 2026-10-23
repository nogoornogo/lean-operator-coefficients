import Physics.FieldTheory.Mass.Surplus.PhysicalCommonCopyModel
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
    ``Physics.PhysicalCommonCopyModel.externalMap,
    ``Physics.PhysicalCommonCopyModel.Species.lightEmbedding,
    ``Physics.PhysicalCommonCopyModel.Species.light_injective,
    ``Physics.PhysicalCommonCopyModel.Species.light_mem_radical,
    ``Physics.PhysicalCommonCopyModel.Species.rangeCoords,
    ``Physics.PhysicalCommonCopyModel.Species.rangeRho,
    ``Physics.PhysicalCommonCopyModel.Species.range_action,
    ``Physics.PhysicalCommonCopyModel.Species.range_light,
    ``Physics.PhysicalCommonCopyModel.speciesOfDirac,
    ``Physics.PhysicalCommonCopyModel.dualExternalEquiv,
    ``Physics.PhysicalCommonCopyModel.Realization.quarkEq,
    ``Physics.PhysicalCommonCopyModel.Realization.upEq,
    ``Physics.PhysicalCommonCopyModel.Realization.electronEq,
    ``Physics.PhysicalCommonCopyModel.Realization.HasLightExterior,
    ``Physics.PhysicalCommonCopyModel.Realization.light_exterior,
    ``Physics.PhysicalCommonCopyModel.Model.arbitrary_mass_light_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"PhysicalCommonCopyModel: {declarations.length} strict transitive axiom checks; no model-layer or original SU5/SU6 imports"
