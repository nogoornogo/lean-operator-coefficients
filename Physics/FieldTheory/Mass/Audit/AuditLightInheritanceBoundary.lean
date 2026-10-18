import Physics.FieldTheory.Mass.LightInheritanceBoundary
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.LightInheritanceBoundary.pairedMass,
    ``GUT.LightInheritanceBoundary.retained_injective,
    ``GUT.LightInheritanceBoundary.restricted_mass_eq,
    ``GUT.LightInheritanceBoundary.paired_mem_radical_iff,
    ``GUT.LightInheritanceBoundary.paired_radical_eq_bot,
    ``GUT.LightInheritanceBoundary.light_not_preserved]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Light inheritance boundary: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Light inheritance boundary: {declarations.length} strict axiom checks passed"
