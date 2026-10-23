import Physics.FieldTheory.Mass.Surplus.AlgebraicCommonCopyKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.AlgebraicCommonCopyKernel.action,
    ``Physics.AlgebraicCommonCopyKernel.simpleToKernel,
    ``Physics.AlgebraicCommonCopyKernel.kernel_semisimple,
    ``Physics.AlgebraicCommonCopyKernel.ofModuleEquiv,
    ``Physics.AlgebraicCommonCopyKernel.exists_common_split,
    ``Physics.AlgebraicCommonCopyKernel.kernel_physical_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"Physics.AlgebraicCommonCopyKernel: {declarations.length} strict transitive axiom checks passed"
