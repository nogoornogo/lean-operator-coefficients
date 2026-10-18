import Physics.FieldTheory.Yukawa.VacuumMassProtection
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``GUT.VacuumMassProtection.mass,
    ``GUT.VacuumMassProtection.cross_apply, ``GUT.VacuumMassProtection.extends_iff,
    ``GUT.VacuumMassProtection.preserves_iff, ``GUT.VacuumMassProtection.family_iff,
    ``GUT.VacuumMassProtection.same_evaluation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Vacuum mass protection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Vacuum mass protection: {declarations.length} strict axiom checks passed"
