import Physics.FieldTheory.Yukawa.ProtectionKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.YukawaProtectionKernel.family,
    ``GUT.YukawaProtectionKernel.obstruction, ``GUT.YukawaProtectionKernel.offset,
    ``GUT.YukawaProtectionKernel.protected_iff,
    ``GUT.YukawaProtectionKernel.protected_iff_mem_kernel,
    ``GUT.YukawaProtectionKernel.fiber_iff,
    ``GUT.YukawaProtectionKernel.exists_iff_range,
    ``GUT.YukawaProtectionKernel.protected_fiber_iff,
    ``GUT.YukawaProtectionKernel.universal_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Protection kernel: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Protection kernel: {declarations.length} strict axiom checks passed"
