import Physics.FieldTheory.Mass.CommonCopyKernel
import Physics.StandardModel.Operators.PhysicalQqueEndpoint
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.PhysicalQqueEndpoint.HasExterior,
    ``GUT.PhysicalQqueEndpoint.of_alternation,
    ``GUT.PhysicalQqueEndpoint.of_exists,
    ``GUT.CommonCopyKernel.familyAction,
    ``GUT.CommonCopyKernel.presentation,
    ``GUT.CommonCopyKernel.difference,
    ``GUT.CommonCopyKernel.difference_character,
    ``GUT.CommonCopyKernel.difference_dimension,
    ``GUT.CommonCopyKernel.leftover,
    ``GUT.CommonCopyKernel.kernel_difference,
    ``GUT.CommonCopyKernel.positive_kernel_split,
    ``GUT.CommonCopyKernel.exists_common_split,
    ``GUT.CommonCopyKernel.kernel_physical_exterior,
    ``GUT.CommonCopyKernel.targetCoordinateContinuity,
    ``GUT.CommonCopyKernel.unitaryTarget,
    ``GUT.CommonCopyKernel.targetEquiv,
    ``GUT.CommonCopyKernel.unitaryTarget_continuous,
    ``GUT.CommonCopyKernel.unitaryTarget_unitary,
    ``GUT.CommonCopyKernel.transportMass,
    ``GUT.CommonCopyKernel.kernelEquiv,
    ``GUT.CommonCopyKernel.exists_common_split_of_continuous,
    ``GUT.CommonCopyKernel.kernel_physical_exterior_of_continuous]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"GUT.CommonCopyKernel: {declarations.length} strict transitive axiom checks passed"
