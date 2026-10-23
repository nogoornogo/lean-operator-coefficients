import Physics.FieldTheory.Mass.Algebra.LightInheritanceBoundary
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.LightInheritanceBoundary.pairedMass,
    ``Physics.LightInheritanceBoundary.retained_injective,
    ``Physics.LightInheritanceBoundary.restricted_mass_eq,
    ``Physics.LightInheritanceBoundary.paired_mem_radical_iff,
    ``Physics.LightInheritanceBoundary.paired_radical_eq_bot,
    ``Physics.LightInheritanceBoundary.light_not_preserved]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Light inheritance boundary: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Light inheritance boundary: {declarations.length} strict axiom checks passed"
