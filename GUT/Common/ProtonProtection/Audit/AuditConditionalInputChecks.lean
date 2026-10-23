import GUT.Common.ProtonProtection.ConditionalInputChecks
import Physics.StandardModel.Operators.Selection.BaryonTrialitySMInput
import Physics.StandardModel.Operators.Selection.InverseCyclicSMYukawa
import Physics.StandardModel.Operators.BaryonOne.Qque.S3YukawaCompatibleQque
import GUT.SU6.SelectionRules.Models.ScalarBlockQque
import Lean.Util.CollectAxioms

open Physics

run_cmd do
  let ds := [``GUT.ConditionalInputChecks.dfpw_b1_forbidden,
    ``GUT.ConditionalInputChecks.dfpw_six_forbidden,
    ``GUT.ConditionalInputChecks.dfpw_subgroup_weinberg_allowed,
    ``GUT.ConditionalInputChecks.lepton_parity_b1_forbidden,
    ``GUT.ConditionalInputChecks.trivial_b1_minimum,
    ``GUT.ConditionalInputChecks.matter_parity_b1_minimum,
    ``GUT.ConditionalInputChecks.matter_parity_six_allowed,
    ``GUT.ConditionalInputChecks.matter_parity_weinberg_allowed,
    ``GUT.ConditionalInputChecks.unbroken_bl_six_forbidden,
    ``GUT.ConditionalInputChecks.unbroken_bl_weinberg_forbidden,
    ``GUT.ConditionalInputChecks.bl_subgroup_b1_minimum,
    ``GUT.ConditionalInputChecks.lepton_parity_six_allowed,
    ``GUT.ConditionalInputChecks.lepton_parity_weinberg_allowed,
    ``GUT.ConditionalInputChecks.sm_even_weinberg_allowed,
    ``GUT.ConditionalInputChecks.proton_hexality_inverse_dictionary,
    ``Physics.BaryonTrialitySMInput.fq,
    ``Physics.BaryonTrialitySMInput.bq,
    ``Physics.BaryonTrialitySMInput.fermion_identity,
    ``Physics.BaryonTrialitySMInput.boson_identity,
    ``Physics.BaryonTrialitySMInput.total,
    ``Physics.BaryonTrialitySMInput.total_identity,
    ``Physics.BaryonTrialitySMInput.copies,
    ``Physics.BaryonTrialitySMInput.flavor,
    ``Physics.BaryonTrialitySMInput.scalarFlavor,
    ``Physics.BaryonTrialitySMInput.field_scalar,
    ``Physics.BaryonTrialitySMInput.scalar_scalar,
    ``Physics.BaryonTrialitySMInput.charge_of_nonzero,
    ``Physics.BaryonTrialitySMInput.baryon_divisible,
    ``Physics.BaryonTrialitySMInput.forbidden_values,
    ``Physics.BaryonTrialitySMInput.all_forbidden,
    ``Physics.BaryonTrialitySMInput.residual_forbidden,
    ``Physics.BaryonTrialitySMInput.component_dictionary,
    ``Physics.InverseCyclicSMYukawa.construction_certificate,
    ``Physics.S3YukawaCompatibleQque.allowed_dictionary,
    ``Physics.S3YukawaCompatibleQque.flavor_map_gates,
    ``Physics.S3QqueTensorSamples.forbidden_permutation_trivial_sign,
    ``Physics.S3QqueTensorSamples.allowed_permutation_sign_sign,
    ``Physics.S3QqueTensorSamples.no_uniform_flavor_dictionary,
    ``GUT.ScalarBlockQque.exists_actual_exterior,
    ``GUT.ProtonProtectionModelControls.baryon_qque_all_flavors,
    ``GUT.ProtonProtectionModelControls.light_parity_selection,
    ``GUT.ProtonProtectionModelControls.gauge_only_qque_allowed,
    ``Physics.BgwZ6Selection.all_forbidden]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conditional input checks: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conditional input checks: {ds.length} strict transitive checks passed"
