import Physics.FieldTheory.Yukawa.Mass.VacuumMassProtection
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [``Physics.VacuumMassProtection.mass,
    ``Physics.VacuumMassProtection.cross_apply, ``Physics.VacuumMassProtection.extends_iff,
    ``Physics.VacuumMassProtection.preserves_iff, ``Physics.VacuumMassProtection.family_iff,
    ``Physics.VacuumMassProtection.same_evaluation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Vacuum mass protection: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Vacuum mass protection: {declarations.length} strict axiom checks passed"
