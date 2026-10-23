import GUT.SU6.SelectionRules.Benchmarks.NonuniformProfileModel

open Physics

/-! Actual finite-residual, non-single-charge realizability for PROFILE-3c.
The target is derived, and both charges occur in actual radical vectors. -/

set_option autoImplicit false

namespace GUT.AuditNonuniformProfileModel

noncomputable section

open NonuniformProfileModel StandardSMCharacterTarget

theorem two_profile_coefficients (i : Fin 15) :
    smCharge nonuniform.profile.profiles i 0 = 1 ∧
      smCharge nonuniform.profile.profiles i (Additive.ofMul signCharacter) = 1 := by
  classical
  simp [nonuniform, model, family, ConcreteSU6PhysicalTarget.smCharge_uniformCharges,
    Ne.symm sign_nontrivial]

/-- The benchmark does not claim to remove the extra vectorlike modes. -/
theorem radical_not_pure_SM : Module.finrank ℂ nonuniform.mass.radical.toSubmodule ≠ 30 := by
  have hd := nonuniform_result.2.1
  omega

#print axioms ScalarResidualSource.action
#print axioms ScalarResidualSource.blockCharacter_eq_of_scalar
#print axioms ScalarResidualSource.chargedSectorSource_uniform
#print axioms ScalarResidualSource.ordinaryChargedSource_uniform
#print axioms ScalarResidualSource.source_character_uniform
#print axioms ScalarResidualSource.fields_character_uniform
#print axioms ScalarResidualSource.fields_character_append
#print axioms target_eq
#print axioms uniform_target_eval
#print axioms charged_fields_character
#print axioms fields_character
#print axioms fields_dual_character
#print axioms mass_hasTarget
#print axioms model
#print axioms fields_finrank
#print axioms model_mass_zero
#print axioms model_radical_finrank
#print axioms two_occupied_assignments
#print axioms not_pure
#print axioms sign_inverse
#print axioms sign_nontrivial
#print axioms nonuniform_not_pure
#print axioms nonuniform_actual_modes
#print axioms nonuniform_result
#print axioms two_profile_coefficients
#print axioms radical_not_pure_SM

end

end GUT.AuditNonuniformProfileModel
