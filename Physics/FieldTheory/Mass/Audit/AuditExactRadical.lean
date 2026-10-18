import Physics.FieldTheory.Mass.ExactRadical
import Physics.FieldTheory.Yukawa.ProtectionKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.ExactRadical.quotientForm,
    ``GUT.ExactRadical.quotientForm_mk, ``GUT.ExactRadical.quotientForm_symmetric,
    ``GUT.ExactRadical.nondegenerate_iff, ``GUT.ExactRadical.exact_iff,
    ``GUT.ExactRadical.family_exists_iff,
    ``GUT.YukawaProtectionKernel.family_protected_iff,
    ``GUT.YukawaProtectionKernel.generated_exact_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exact radical: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact radical: {declarations.length} strict axiom checks passed"
