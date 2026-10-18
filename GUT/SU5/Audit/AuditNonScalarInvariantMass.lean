import GUT.SU5.SelectionRules.NonScalarInvariantMass
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT.SU6).isPrefixOf (SourceLayout.originalModule mod) then
      throwError "Unexpected original SU6 dependency: {mod}"
  let declarations := [
    ``GUT.SU5.NonScalarInvariantMass.tensorCoordinates,
    ``GUT.SU5.NonScalarInvariantMass.tensorCoordinates_tmul,
    ``GUT.SU5.NonScalarInvariantMass.tensorCopiesEquiv,
    ``GUT.SU5.NonScalarInvariantMass.tenCoordinates,
    ``GUT.SU5.NonScalarInvariantMass.sourceCoordinates,
    ``GUT.SU5.NonScalarInvariantMass.targetCoordinates,
    ``GUT.SU5.NonScalarInvariantMass.source_no_pairings,
    ``GUT.SU5.NonScalarInvariantMass.target_dual_no_pairings,
    ``GUT.SU5.NonScalarInvariantMass.normal_form,
    ``GUT.SU5.NonScalarInvariantMass.coordinateMap,
    ``GUT.SU5.NonScalarInvariantMass.speciesLinear,
    ``GUT.SU5.NonScalarInvariantMass.speciesLinear_coordinates,
    ``GUT.SU5.NonScalarInvariantMass.coordinate_reconstruction,
    ``GUT.SU5.NonScalarInvariantMass.weighted_decompose,
    ``GUT.SU5.NonScalarInvariantMass.reconstructedLinear,
    ``GUT.SU5.NonScalarInvariantMass.reconstructedLinear_eq,
    ``GUT.SU5.NonScalarInvariantMass.quark_pure,
    ``GUT.SU5.NonScalarInvariantMass.up_pure,
    ``GUT.SU5.NonScalarInvariantMass.electron_pure,
    ``GUT.SU5.NonScalarInvariantMass.tmul_injective,
    ``GUT.SU5.NonScalarInvariantMass.species_equivariant,
    ``GUT.SU5.NonScalarInvariantMass.quarkMap,
    ``GUT.SU5.NonScalarInvariantMass.upMap,
    ``GUT.SU5.NonScalarInvariantMass.electronMap,
    ``GUT.SU5.NonScalarInvariantMass.massMap_eq,
    ``GUT.SU5.NonScalarInvariantMass.species_normal_form,
    ``GUT.SU5.NonScalarInvariantMass.arbitrary_mass_light_exterior,
    ``GUT.SU5.NonScalarInvariantMass.arbitrary_mass_light_exterior_of_continuous,
    ``GUT.SU5.NonScalarInvariantMass.arbitrary_mass_light_exterior_of_semisimple]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"GUT.SU5.NonScalarInvariantMass: {declarations.length} strict transitive axiom checks passed"
