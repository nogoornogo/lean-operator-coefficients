import GUT.SU6.SelectionRules.Models.ChargeProfileObstruction
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU6ChargeProfileObstruction.singleProfile,
    ``GUT.SU6ChargeProfileObstruction.singleProfile_injective,
    ``GUT.SU6ChargeProfileObstruction.equal_profiles_force_neutral]
  for decl in ds do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Charge profile: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Charge profile: {ds.length} strict transitive checks passed"
