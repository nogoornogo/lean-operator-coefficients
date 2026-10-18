import GUT.SU5.SelectionRules.ActualFullFamilyMassExistence
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.ActualFullFamilyMassExistence.positive,
    ``GUT.SU5.ActualFullFamilyMassExistence.sourceSplit,
    ``GUT.SU5.ActualFullFamilyMassExistence.counts_positive,
    ``GUT.SU5.ActualFullFamilyMassExistence.exists_mass_of_counts,
    ``GUT.SU5.ActualFullFamilyMassExistence.exists_mass_iff,
    ``GUT.SU5.ActualFullFamilyMassExistence.zero_mass_control]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Full-family mass existence: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Full-family mass existence: {ds.length} strict transitive checks passed"
