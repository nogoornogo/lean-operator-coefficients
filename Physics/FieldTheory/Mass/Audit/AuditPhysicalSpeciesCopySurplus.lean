import Physics.FieldTheory.Mass.PhysicalSpeciesCopySurplus
import Physics.FieldTheory.Mass.SpeciesSectorPresentation
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
    ``GUT.PhysicalSpeciesCopySurplus.Realization.quarkEq,
    ``GUT.PhysicalSpeciesCopySurplus.Realization.upEq,
    ``GUT.PhysicalSpeciesCopySurplus.Realization.electronEq,
    ``GUT.PhysicalSpeciesCopySurplus.Realization.HasLightExterior,
    ``GUT.PhysicalSpeciesCopySurplus.Realization.light_exterior,
    ``GUT.PhysicalSpeciesCopySurplus.Model.arbitrary_mass_light_exterior,
    ``GUT.SpeciesSectorPresentation.ofIrreducible,
    ``GUT.SpeciesSectorPresentation.Presentation.source,
    ``GUT.SpeciesSectorPresentation.Presentation.opposite,
    ``GUT.SpeciesSectorPresentation.Presentation.rest,
    ``GUT.SpeciesSectorPresentation.Presentation.oppositeProjection,
    ``GUT.SpeciesSectorPresentation.Presentation.rawMass,
    ``GUT.SpeciesSectorPresentation.Presentation.massMap,
    ``GUT.SpeciesSectorPresentation.Presentation.dualField,
    ``GUT.SpeciesSectorPresentation.Presentation.mass_column,
    ``GUT.SpeciesSectorPresentation.Presentation.copyMap,
    ``GUT.SpeciesSectorPresentation.Presentation.mass_factor,
    ``GUT.SpeciesSectorPresentation.Presentation.species,
    ``GUT.SpeciesSectorPresentation.modelOfPresentations]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"SpeciesCopySurplus physics: {declarations.length} strict transitive checks; layer imports checked"
