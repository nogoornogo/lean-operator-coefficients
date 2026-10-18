import Physics.FieldTheory.Mass.HomSurplusMass
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.HomSurplusMass.noPairings_finrank_zero,
    ``GUT.HomSurplusMass.source_multiplicity,
    ``GUT.HomSurplusMass.target_multiplicity,
    ``GUT.HomSurplusMass.arbitrary_mass_survival,
    ``GUT.HomSurplusMass.no_light_species_necessary,
    ``GUT.HomSurplusMass.radical_hom_zero,
    ``GUT.HomSurplusMass.radical_multiplicity_bound]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Hom mass surplus: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Hom mass surplus: {ds.length} strict transitive checks passed"
