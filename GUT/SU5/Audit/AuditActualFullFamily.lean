import GUT.SU5.SelectionRules.ActualFullFamilyQque
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.SU5.CyclicHypercharge.character_injective,
    ``GUT.SU5.CyclicHypercharge.eval_injective,
    ``GUT.SU5.CyclicHypercharge.eval_dual,
    ``GUT.SU5.CyclicHypercharge.eval_zsmul,
    ``GUT.SU5.ActualHyperchargeProfiles.five_character,
    ``GUT.SU5.ActualHyperchargeProfiles.ten_character,
    ``GUT.SU5.ActualHyperchargeProfiles.exterior_character,
    ``GUT.SU5.ActualHyperchargeProfiles.symmetric_character,
    ``GUT.SU5.ActualHyperchargeProfiles.original_ambient_character,
    ``GUT.SU5.ActualHyperchargeProfiles.forty_character,
    ``GUT.SU5.ActualHyperchargeProfiles.fifty_character,
    ``GUT.SU5.ActualHyperchargeProfiles.five_coefficients,
    ``GUT.SU5.ActualHyperchargeProfiles.ten_coefficients,
    ``GUT.SU5.ActualHyperchargeProfiles.exterior_three_coefficients,
    ``GUT.SU5.ActualHyperchargeProfiles.exterior_four_coefficients,
    ``GUT.SU5.ActualHyperchargeProfiles.forty_coefficients,
    ``GUT.SU5.ActualHyperchargeProfiles.fifty_coefficients,
    ``GUT.SU5.ActualFullFamilyIndex.bar_character,
    ``GUT.SU5.ActualFullFamilyIndex.source_character,
    ``GUT.SU5.ActualFullFamilyIndex.field_character,
    ``GUT.SU5.ActualFullFamilyIndex.sm_character,
    ``GUT.SU5.ActualFullFamilyIndex.light_index_of_exact_sm,
    ``GUT.SU5.ActualFullFamilyIndex.source_index_from_mass,
    ``GUT.SU5.ActualFullFamilyIndex.row_table,
    ``GUT.SU5.ActualFullFamilyIndex.index_rows,
    ``GUT.SU5.ActualFullFamilyIndex.sm_index_rows,
    ``GUT.SU5.ActualFullFamilyIndex.net_constraints,
    ``GUT.SU5.ActualFullFamilyIndex.net_constraints_of_exact_sm,
    ``GUT.SU5.ActualFullFamilyIndex.copy_constraint_prefilter,
    ``GUT.SU5.ActualFullFamilyQque.qGeneration_injective,
    ``GUT.SU5.ActualFullFamilyQque.uGeneration_injective,
    ``GUT.SU5.ActualFullFamilyQque.eGeneration_injective,
    ``GUT.SU5.ActualFullFamilyQque.LightTriplet.hasCoefficient,
    ``GUT.SU5.ActualFullFamilyQque.selectCopy_injective,
    ``GUT.SU5.ActualFullFamilyQque.tripletOfExactSM,
    ``GUT.SU5.ActualFullFamilyQque.exact_sm_not_forbidden,
    ``GUT.SU5.ActualFullFamilyQque.full_family_exclusion,
    ``GUT.SU5.ActualFullFamilyQque.no_sm_prohibiting_input]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Actual full family: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Actual full family: {ds.length} strict transitive checks passed"
