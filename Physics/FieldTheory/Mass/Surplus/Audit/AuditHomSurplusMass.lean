import Physics.FieldTheory.Mass.Surplus.HomSurplusMass
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``Physics.HomSurplusMass.noPairings_finrank_zero,
    ``Physics.HomSurplusMass.source_multiplicity,
    ``Physics.HomSurplusMass.target_multiplicity,
    ``Physics.HomSurplusMass.arbitrary_mass_survival,
    ``Physics.HomSurplusMass.no_light_species_necessary,
    ``Physics.HomSurplusMass.radical_hom_zero,
    ``Physics.HomSurplusMass.radical_multiplicity_bound]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Hom mass surplus: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Hom mass surplus: {ds.length} strict transitive checks passed"
