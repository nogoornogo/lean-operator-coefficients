import Physics.StandardModel.Operators.Dipole.CyclicSelectorDipoleSelection
import Physics.FieldTheory.Mass.Surplus.BalancedSpeciesSurplusControl
import Physics.StandardModel.Operators.Selection.AdmittedCyclicSMProhibition
import Lean.Util.CollectAxioms
run_cmd do
  let ds := [``Physics.CyclicSelectorDipoleSelection.SupportedMatch,
    ``Physics.CyclicSelectorDipoleSelection.coordinate_zero,
    ``Physics.CyclicSelectorDipoleSelection.evaluation_expand,
    ``Physics.CyclicSelectorDipoleSelection.selected_allowed_iff,
    ``Physics.CyclicSelectorDipoleSelection.selected_forbidden_iff,
    ``Physics.CyclicSelectorDipoleSelection.zero_source_forbidden,
    ``Physics.CyclicSelectorDipoleSelection.zero_target_forbidden,
    ``Physics.BalancedSpeciesSurplusControl.qAction,
    ``Physics.BalancedSpeciesSurplusControl.uAction,
    ``Physics.BalancedSpeciesSurplusControl.eAction,
    ``Physics.BalancedSpeciesSurplusControl.Field,
    ``Physics.BalancedSpeciesSurplusControl.fields,
    ``Physics.BalancedSpeciesSurplusControl.mass,
    ``Physics.BalancedSpeciesSurplusControl.zeroSpecies,
    ``Physics.BalancedSpeciesSurplusControl.realization,
    ``Physics.BalancedSpeciesSurplusControl.zeroKernelSplit,
    ``Physics.BalancedSpeciesSurplusControl.physical_light_coefficient,
    ``Physics.BalancedSpeciesSurplusControl.no_surplus,
    ``Physics.BalancedSpeciesSurplusControl.not_forbidden,
    ``Physics.BalancedSpeciesSurplusControl.converse_counterexample,
    ``Physics.AdmittedCyclicSMProhibition.forbidden_iff,
    ``Physics.AdmittedCyclicSMProhibition.all_forbidden_iff,
    ``Physics.AdmittedCyclicSMProhibition.odd_coefficients_zero,
    ``Physics.AdmittedCyclicSMProhibition.tripleQ,
    ``Physics.AdmittedCyclicSMProhibition.neutral_b1_content,
    ``Physics.AdmittedCyclicSMProhibition.raw_filter_not_necessary]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Physics converse boundaries: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Physics converse boundaries: {ds.length} strict transitive checks passed"
