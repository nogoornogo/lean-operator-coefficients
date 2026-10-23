import Physics.FieldTheory.Yukawa.Mass.ProtectionKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``Physics.YukawaProtectionKernel.family,
    ``Physics.YukawaProtectionKernel.obstruction, ``Physics.YukawaProtectionKernel.offset,
    ``Physics.YukawaProtectionKernel.protected_iff,
    ``Physics.YukawaProtectionKernel.protected_iff_mem_kernel,
    ``Physics.YukawaProtectionKernel.fiber_iff,
    ``Physics.YukawaProtectionKernel.exists_iff_range,
    ``Physics.YukawaProtectionKernel.protected_fiber_iff,
    ``Physics.YukawaProtectionKernel.universal_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Protection kernel: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Protection kernel: {declarations.length} strict axiom checks passed"
