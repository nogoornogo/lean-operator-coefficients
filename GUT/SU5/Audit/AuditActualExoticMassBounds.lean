import GUT.SU5.SelectionRules.ActualExoticMassBounds
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.ActualExoticMassBounds.source_no_pairings,
    ``GUT.SU5.ActualExoticMassBounds.source_q_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.source_u_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.source_e_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.field_q_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.mass_target_q_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.field_u_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.mass_target_u_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.field_e_multiplicity,
    ``GUT.SU5.ActualExoticMassBounds.arbitrary_mass_lower_bounds,
    ``GUT.SU5.ActualExoticMassBounds.arbitrary_mass_q_u_survive,
    ``GUT.SU5.ActualExoticMassBounds.arbitrary_mass_no_electron,
    ``GUT.SU5.ActualExoticMassBounds.no_light_q_necessary,
    ``GUT.SU5.ActualExoticMassBounds.no_light_u_necessary,
    ``GUT.SU5.ActualExoticMassBounds.no_exact_sm_light]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Actual exotic mass: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Actual exotic mass: {ds.length} strict transitive checks passed"
