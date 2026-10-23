import Physics.FieldTheory.Mass.Surplus.CommonCopyKernel
import Physics.StandardModel.Operators.BaryonOne.Qque.PhysicalQqueEndpoint
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.PhysicalQqueEndpoint.HasExterior,
    ``Physics.PhysicalQqueEndpoint.of_alternation,
    ``Physics.PhysicalQqueEndpoint.of_exists,
    ``Physics.CommonCopyKernel.familyAction,
    ``Physics.CommonCopyKernel.presentation,
    ``Physics.CommonCopyKernel.difference,
    ``Physics.CommonCopyKernel.difference_character,
    ``Physics.CommonCopyKernel.difference_dimension,
    ``Physics.CommonCopyKernel.leftover,
    ``Physics.CommonCopyKernel.kernel_difference,
    ``Physics.CommonCopyKernel.positive_kernel_split,
    ``Physics.CommonCopyKernel.exists_common_split,
    ``Physics.CommonCopyKernel.kernel_physical_exterior,
    ``Physics.CommonCopyKernel.targetCoordinateContinuity,
    ``Physics.CommonCopyKernel.unitaryTarget,
    ``Physics.CommonCopyKernel.targetEquiv,
    ``Physics.CommonCopyKernel.unitaryTarget_continuous,
    ``Physics.CommonCopyKernel.unitaryTarget_unitary,
    ``Physics.CommonCopyKernel.transportMass,
    ``Physics.CommonCopyKernel.kernelEquiv,
    ``Physics.CommonCopyKernel.exists_common_split_of_continuous,
    ``Physics.CommonCopyKernel.kernel_physical_exterior_of_continuous]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"Physics.CommonCopyKernel: {declarations.length} strict transitive axiom checks passed"
