import GUT.SU6.Yukawa.GeneratedMassFamily
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.SU6GeneratedMassFamily.allCouplings,
    ``GUT.SU6GeneratedMassFamily.coupling,
    ``GUT.SU6GeneratedMassFamily.vacuum_fixed,
    ``GUT.SU6GeneratedMassFamily.mass_eq,
    ``GUT.SU6GeneratedMassFamily.light_preserved,
    ``GUT.SU6GeneratedMassFamily.lightEquiv,
    ``GUT.SU6GeneratedMassFamily.zero_mass,
    ``GUT.SU6GeneratedMassFamily.zeroLightEquiv,
    ``GUT.SU6GeneratedMassFamily.radical_finrank,
    ``GUT.SU6GeneratedMassFamily.mass_nonzero_iff,
    ``GUT.SU6GeneratedMassFamily.fifteen_iff,
    ``GUT.SU6GeneratedMassFamily.light_character,
    ``GUT.SU6GeneratedMassFamily.original_mass,
    ``GUT.SU6GeneratedMassFamily.coupling_off,
    ``GUT.SU6GeneratedMassFamily.vacuum_off]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Generated SU6 mass family: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Generated SU6 mass family: {declarations.length} strict axiom checks passed"
