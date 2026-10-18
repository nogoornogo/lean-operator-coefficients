import GUT.Common.ProtonProtection.ConditionalInputChecks
import Physics.StandardModel.Operators.BaryonTrialitySMInput
import Physics.StandardModel.Operators.InverseCyclicSMYukawa
import Physics.StandardModel.Operators.S3YukawaCompatibleQque
import GUT.SU6.SelectionRules.Models.ScalarBlockQque
import Lean.Util.CollectAxioms

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
    ``GUT.BaryonTrialitySMInput.fq,
    ``GUT.BaryonTrialitySMInput.bq,
    ``GUT.BaryonTrialitySMInput.fermion_identity,
    ``GUT.BaryonTrialitySMInput.boson_identity,
    ``GUT.BaryonTrialitySMInput.total,
    ``GUT.BaryonTrialitySMInput.total_identity,
    ``GUT.BaryonTrialitySMInput.copies,
    ``GUT.BaryonTrialitySMInput.flavor,
    ``GUT.BaryonTrialitySMInput.scalarFlavor,
    ``GUT.BaryonTrialitySMInput.field_scalar,
    ``GUT.BaryonTrialitySMInput.scalar_scalar,
    ``GUT.BaryonTrialitySMInput.charge_of_nonzero,
    ``GUT.BaryonTrialitySMInput.baryon_divisible,
    ``GUT.BaryonTrialitySMInput.forbidden_values,
    ``GUT.BaryonTrialitySMInput.all_forbidden,
    ``GUT.BaryonTrialitySMInput.residual_forbidden,
    ``GUT.BaryonTrialitySMInput.component_dictionary,
    ``GUT.InverseCyclicSMYukawa.construction_certificate,
    ``GUT.S3YukawaCompatibleQque.allowed_dictionary,
    ``GUT.S3YukawaCompatibleQque.flavor_map_gates,
    ``GUT.S3QqueTensorSamples.forbidden_permutation_trivial_sign,
    ``GUT.S3QqueTensorSamples.allowed_permutation_sign_sign,
    ``GUT.S3QqueTensorSamples.no_uniform_flavor_dictionary,
    ``GUT.ScalarBlockQque.exists_actual_exterior,
    ``GUT.ProtonProtectionModelControls.baryon_qque_all_flavors,
    ``GUT.ProtonProtectionModelControls.light_parity_selection,
    ``GUT.ProtonProtectionModelControls.gauge_only_qque_allowed,
    ``GUT.BgwZ6Selection.all_forbidden]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conditional input checks: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conditional input checks: {ds.length} strict transitive checks passed"
