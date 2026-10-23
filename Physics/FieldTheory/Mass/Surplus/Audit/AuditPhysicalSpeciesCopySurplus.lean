import Physics.FieldTheory.Mass.Surplus.PhysicalSpeciesCopySurplus
import Physics.FieldTheory.Mass.Surplus.SpeciesSectorPresentation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected upper-layer import: {mod}"
    let origin := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf origin || (`GUT.SU6).isPrefixOf origin then
      throwError "Unexpected original SU5/SU6 import: {mod}"
  let declarations := [
    ``Physics.PhysicalSpeciesCopySurplus.Realization.quarkEq,
    ``Physics.PhysicalSpeciesCopySurplus.Realization.upEq,
    ``Physics.PhysicalSpeciesCopySurplus.Realization.electronEq,
    ``Physics.PhysicalSpeciesCopySurplus.Realization.HasLightExterior,
    ``Physics.PhysicalSpeciesCopySurplus.Realization.light_exterior,
    ``Physics.PhysicalSpeciesCopySurplus.Model.arbitrary_mass_light_exterior,
    ``Physics.SpeciesSectorPresentation.ofIrreducible,
    ``Physics.SpeciesSectorPresentation.Presentation.source,
    ``Physics.SpeciesSectorPresentation.Presentation.opposite,
    ``Physics.SpeciesSectorPresentation.Presentation.rest,
    ``Physics.SpeciesSectorPresentation.Presentation.oppositeProjection,
    ``Physics.SpeciesSectorPresentation.Presentation.rawMass,
    ``Physics.SpeciesSectorPresentation.Presentation.massMap,
    ``Physics.SpeciesSectorPresentation.Presentation.dualField,
    ``Physics.SpeciesSectorPresentation.Presentation.mass_column,
    ``Physics.SpeciesSectorPresentation.Presentation.copyMap,
    ``Physics.SpeciesSectorPresentation.Presentation.mass_factor,
    ``Physics.SpeciesSectorPresentation.Presentation.species,
    ``Physics.SpeciesSectorPresentation.modelOfPresentations]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"SpeciesCopySurplus physics: {declarations.length} strict transitive checks; layer imports checked"
