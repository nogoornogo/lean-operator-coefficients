import GUT.SU5.Branching.FortyHyperchargeExclusion
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.FortyHyperchargeExclusion.five_basis_action,
    ``GUT.SU5.FortyHyperchargeExclusion.ambient_action,
    ``GUT.SU5.FortyHyperchargeExclusion.coefficient_separated,
    ``GUT.SU5.FortyHyperchargeExclusion.ambient_no_eigen,
    ``GUT.SU5.FortyHyperchargeExclusion.original_no_eigen,
    ``GUT.SU5.FortyHyperchargeExclusion.original_hom_zero,
    ``GUT.SU5.FortyHyperchargeExclusion.no_pairings_forty,
    ``GUT.SU5.FortyHyperchargeExclusion.forty_eq_actual_restriction,
    ``GUT.SU5.FortyHyperchargeExclusion.selected_no_pairings,
    ``GUT.SU5.FortyHyperchargeExclusion.original_shift_surjective,
    ``GUT.SU5.FortyHyperchargeExclusion.forty_no_opposite_eigen,
    ``GUT.SU5.FortyHyperchargeExclusion.opposite_hom_zero,
    ``GUT.SU5.FortyHyperchargeExclusion.opposite_hom_finrank_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Forty hypercharge: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Forty hypercharge: {ds.length} strict transitive checks passed"
