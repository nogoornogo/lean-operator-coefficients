import GUT.SU5.SelectionRules.MatrixTenMass
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Strict transitive audit for arbitrary-copy mass kernels and physical qque. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT.SU6).isPrefixOf (SourceLayout.originalModule mod) then
      throwError "SU5 matrix mass imports SU6: {mod}"
  let declarations := [
    ``GUT.SU5.MatrixTenMass.row,
    ``GUT.SU5.MatrixTenMass.copies,
    ``GUT.SU5.MatrixTenMass.sourceRho,
    ``GUT.SU5.MatrixTenMass.targetRho,
    ``GUT.SU5.MatrixTenMass.fieldsRho,
    ``GUT.SU5.MatrixTenMass.massMap,
    ``GUT.SU5.MatrixTenMass.mass,
    ``GUT.SU5.MatrixTenMass.mem_radical_iff,
    ``GUT.SU5.MatrixTenMass.matrixMap,
    ``GUT.SU5.MatrixTenMass.kernel_dimension,
    ``GUT.SU5.MatrixTenMass.exists_kernel_vector,
    ``GUT.SU5.MatrixTenMass.kernels,
    ``GUT.SU5.MatrixTenMass.lightMap,
    ``GUT.SU5.MatrixTenMass.lightMap_injective,
    ``GUT.SU5.MatrixTenMass.quarkLinear,
    ``GUT.SU5.MatrixTenMass.quark_injective,
    ``GUT.SU5.MatrixTenMass.quark_light,
    ``GUT.SU5.MatrixTenMass.quark_action,
    ``GUT.SU5.MatrixTenMass.upLinear,
    ``GUT.SU5.MatrixTenMass.up_injective,
    ``GUT.SU5.MatrixTenMass.up_light,
    ``GUT.SU5.MatrixTenMass.up_action,
    ``GUT.SU5.MatrixTenMass.electronLinear,
    ``GUT.SU5.MatrixTenMass.electron_injective,
    ``GUT.SU5.MatrixTenMass.electron_light,
    ``GUT.SU5.MatrixTenMass.electron_action,
    ``GUT.SU5.MatrixTenMass.rangeCoords,
    ``GUT.SU5.MatrixTenMass.rangeRho,
    ``GUT.SU5.MatrixTenMass.range_coords,
    ``GUT.SU5.MatrixTenMass.range_action,
    ``GUT.SU5.MatrixTenMass.charges,
    ``GUT.SU5.MatrixTenMass.neutral,
    ``GUT.SU5.MatrixTenMass.quarkRho,
    ``GUT.SU5.MatrixTenMass.upLeftRho,
    ``GUT.SU5.MatrixTenMass.electronLeftRho,
    ``GUT.SU5.MatrixTenMass.quarkSpace_light,
    ``GUT.SU5.MatrixTenMass.quarkSpace_action,
    ``GUT.SU5.MatrixTenMass.upSpace_light,
    ``GUT.SU5.MatrixTenMass.upSpace_action,
    ``GUT.SU5.MatrixTenMass.electronSpace_light,
    ``GUT.SU5.MatrixTenMass.electronSpace_action,
    ``GUT.SU5.MatrixTenMass.quarkEq,
    ``GUT.SU5.MatrixTenMass.upEq,
    ``GUT.SU5.MatrixTenMass.electronEq,
    ``GUT.SU5.MatrixTenMass.exists_actual_exterior,
    ``GUT.SU5.MatrixTenMass.exists_light_exterior,
    ``GUT.SU5.MatrixTenMass.rectangular_light_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SU5 matrix mass: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"SU5 matrix mass: {declarations.length} strict transitive axiom checks passed"
