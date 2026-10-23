import Physics.FieldTheory.Mass.Algebra.ExactRadical
import Physics.FieldTheory.Yukawa.Mass.ProtectionKernel
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``Physics.ExactRadical.quotientForm,
    ``Physics.ExactRadical.quotientForm_mk, ``Physics.ExactRadical.quotientForm_symmetric,
    ``Physics.ExactRadical.nondegenerate_iff, ``Physics.ExactRadical.exact_iff,
    ``Physics.ExactRadical.family_exists_iff,
    ``Physics.YukawaProtectionKernel.family_protected_iff,
    ``Physics.YukawaProtectionKernel.generated_exact_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exact radical: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact radical: {declarations.length} strict axiom checks passed"
