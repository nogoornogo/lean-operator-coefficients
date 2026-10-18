import Physics.FieldTheory.Mass.AlgebraicCommonCopyKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.AlgebraicCommonCopyKernel.action,
    ``GUT.AlgebraicCommonCopyKernel.simpleToKernel,
    ``GUT.AlgebraicCommonCopyKernel.kernel_semisimple,
    ``GUT.AlgebraicCommonCopyKernel.ofModuleEquiv,
    ``GUT.AlgebraicCommonCopyKernel.exists_common_split,
    ``GUT.AlgebraicCommonCopyKernel.kernel_physical_exterior]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom: {decl}: {ax}"
  Lean.logInfo m!"GUT.AlgebraicCommonCopyKernel: {declarations.length} strict transitive axiom checks passed"
