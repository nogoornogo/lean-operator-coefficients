import GUT.SU5.Branching.ExoticHyperchargeBasis
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.ExoticHyperchargeBasis.basis_action,
    ``GUT.SU5.ExoticHyperchargeBasis.root_zpow,
    ``GUT.SU5.ExoticHyperchargeBasis.symmetric_action,
    ``GUT.SU5.ExoticHyperchargeBasis.coefficient_separated,
    ``GUT.SU5.ExoticHyperchargeBasis.symmetric_no_eigen,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_hom_zero,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_no_eigen,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_shift_surjective,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_dual_no_eigen,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_no_pairings,
    ``GUT.SU5.ExoticHyperchargeBasis.selected_no_pairings,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_dual_no_pairings,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_dual_hom_zero,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_hom_finrank_zero,
    ``GUT.SU5.ExoticHyperchargeBasis.fifty_dual_hom_finrank_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exotic hypercharge: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exotic hypercharge: {ds.length} strict transitive checks passed"
