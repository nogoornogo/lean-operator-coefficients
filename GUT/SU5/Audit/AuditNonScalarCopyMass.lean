import GUT.SU5.SelectionRules.NonScalarCopyMass
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT.SU6).isPrefixOf (SourceLayout.originalModule mod) then
      throwError "Unexpected original SU6 dependency: {mod}"
  let declarations := [
    ``GUT.SU5.NonScalarCopyMass.externalMap,
    ``GUT.SU5.NonScalarCopyMass.barAction,
    ``GUT.SU5.NonScalarCopyMass.sourceRho,
    ``GUT.SU5.NonScalarCopyMass.targetRho,
    ``GUT.SU5.NonScalarCopyMass.fieldsRho,
    ``GUT.SU5.NonScalarCopyMass.upWeight,
    ``GUT.SU5.NonScalarCopyMass.quarkWeight,
    ``GUT.SU5.NonScalarCopyMass.electronWeight,
    ``GUT.SU5.NonScalarCopyMass.massMap,
    ``GUT.SU5.NonScalarCopyMass.mass,
    ``GUT.SU5.NonScalarCopyMass.mem_radical_iff,
    ``GUT.SU5.NonScalarCopyMass.kernelInclusion,
    ``GUT.SU5.NonScalarCopyMass.quarkTenMap,
    ``GUT.SU5.NonScalarCopyMass.quarkEmbedding,
    ``GUT.SU5.NonScalarCopyMass.quark_injective,
    ``GUT.SU5.NonScalarCopyMass.quark_light,
    ``GUT.SU5.NonScalarCopyMass.upTenMap,
    ``GUT.SU5.NonScalarCopyMass.upEmbedding,
    ``GUT.SU5.NonScalarCopyMass.up_injective,
    ``GUT.SU5.NonScalarCopyMass.up_light,
    ``GUT.SU5.NonScalarCopyMass.electronTenMap,
    ``GUT.SU5.NonScalarCopyMass.electronEmbedding,
    ``GUT.SU5.NonScalarCopyMass.electron_injective,
    ``GUT.SU5.NonScalarCopyMass.electron_light,
    ``GUT.SU5.NonScalarCopyMass.dualExternalEquiv,
    ``GUT.SU5.NonScalarCopyMass.rangeCoords,
    ``GUT.SU5.NonScalarCopyMass.rangeRho,
    ``GUT.SU5.NonScalarCopyMass.range_action,
    ``GUT.SU5.NonScalarCopyMass.quarkRho,
    ``GUT.SU5.NonScalarCopyMass.upLeftRho,
    ``GUT.SU5.NonScalarCopyMass.electronLeftRho,
    ``GUT.SU5.NonScalarCopyMass.quarkEq,
    ``GUT.SU5.NonScalarCopyMass.upEq,
    ``GUT.SU5.NonScalarCopyMass.electronEq,
    ``GUT.SU5.NonScalarCopyMass.kernel_physical_exterior,
    ``GUT.SU5.NonScalarCopyMass.exists_actual_exterior,
    ``GUT.SU5.NonScalarCopyMass.exists_light_exterior,
    ``GUT.SU5.NonScalarCopyMass.exists_actual_exterior_of_continuous,
    ``GUT.SU5.NonScalarCopyMass.exists_light_exterior_of_continuous,
    ``GUT.SU5.NonScalarCopyMass.exists_actual_exterior_of_semisimple,
    ``GUT.SU5.NonScalarCopyMass.exists_light_exterior_of_semisimple]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"GUT.SU5.NonScalarCopyMass: {declarations.length} strict transitive axiom checks passed"
