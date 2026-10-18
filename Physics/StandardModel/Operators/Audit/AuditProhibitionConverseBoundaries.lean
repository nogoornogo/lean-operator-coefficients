import Physics.StandardModel.Operators.CyclicSelectorDipoleSelection
import Physics.FieldTheory.Mass.BalancedSpeciesSurplusControl
import Physics.StandardModel.Operators.AdmittedCyclicSMProhibition
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``GUT.CyclicSelectorDipoleSelection.SupportedMatch,
    ``GUT.CyclicSelectorDipoleSelection.coordinate_zero,
    ``GUT.CyclicSelectorDipoleSelection.evaluation_expand,
    ``GUT.CyclicSelectorDipoleSelection.selected_allowed_iff,
    ``GUT.CyclicSelectorDipoleSelection.selected_forbidden_iff,
    ``GUT.CyclicSelectorDipoleSelection.zero_source_forbidden,
    ``GUT.CyclicSelectorDipoleSelection.zero_target_forbidden,
    ``GUT.BalancedSpeciesSurplusControl.qAction,
    ``GUT.BalancedSpeciesSurplusControl.uAction,
    ``GUT.BalancedSpeciesSurplusControl.eAction,
    ``GUT.BalancedSpeciesSurplusControl.Field,
    ``GUT.BalancedSpeciesSurplusControl.fields,
    ``GUT.BalancedSpeciesSurplusControl.mass,
    ``GUT.BalancedSpeciesSurplusControl.zeroSpecies,
    ``GUT.BalancedSpeciesSurplusControl.realization,
    ``GUT.BalancedSpeciesSurplusControl.zeroKernelSplit,
    ``GUT.BalancedSpeciesSurplusControl.physical_light_coefficient,
    ``GUT.BalancedSpeciesSurplusControl.no_surplus,
    ``GUT.BalancedSpeciesSurplusControl.not_forbidden,
    ``GUT.BalancedSpeciesSurplusControl.converse_counterexample,
    ``GUT.AdmittedCyclicSMProhibition.forbidden_iff,
    ``GUT.AdmittedCyclicSMProhibition.all_forbidden_iff,
    ``GUT.AdmittedCyclicSMProhibition.odd_coefficients_zero,
    ``GUT.AdmittedCyclicSMProhibition.tripleQ,
    ``GUT.AdmittedCyclicSMProhibition.neutral_b1_content,
    ``GUT.AdmittedCyclicSMProhibition.raw_filter_not_necessary]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Physics converse boundaries: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Physics converse boundaries: {ds.length} strict transitive checks passed"
