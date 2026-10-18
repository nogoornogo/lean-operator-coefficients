import Math.Audit.ImportOrigin
import GUT.SU5.SelectionRules.ChargeProfiles
import GUT.SU5.Audit.AuditMatterSource

open Math

/-! Actual generation mixing, repeated characters, and zero-dimensional
controls for the common profile adapter. Full field-map support is retained. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "SU(5) charge-profile audit imports SU(6): {mod}"

namespace GUT.SU5.AuditChargeProfiles

noncomputable section

open MatterSource ResidualSectors SupportedFields ChargeProfiles AuditMatterSource

theorem repeated_profile : kindProfile mixingSource .barFive 0 = 2 := by
  rw [kindProfile_apply]
  change Module.finrank ℂ (sector mixingSource .barFive 1).toSubmodule = 2
  rw [repeated_barFive_character]
  simp

theorem two_occupied_characters :
    0 < kindProfile mixingSource .ten 0 ∧
      0 < kindProfile mixingSource .ten (Additive.ofMul oddCharacter) ∧
      (Additive.ofMul oddCharacter : FiniteAbelianChargeSectors.ChargeLabel ℤˣ) ≠ 0 := by
  have hv (z : ℂ) : (WithLp.toLp 2 (![1, z] : Fin 2 → ℂ) : Generations 2) ≠ 0 := by
    intro h
    have he := congrArg (fun v : Generations 2 => v 0) h
    norm_num at he
  refine ⟨kindProfile_pos_of_mode (⟨1, _, hv 1, even_mode⟩ : Mode mixingSource .ten),
    kindProfile_pos_of_mode (⟨oddCharacter, _, hv (-1), odd_mode⟩ : Mode mixingSource .ten), ?_⟩
  intro h
  have he := congrArg (fun q : FiniteAbelianChargeSectors.ChargeLabel ℤˣ =>
    (q.toMul (-1) : ℂ)) h
  norm_num [oddCharacter] at he

theorem zero_profile {H : Type*} [CommGroup H] (R : OrdinaryAction H 0) (i : Kind) :
    kindProfile R i = 0 := by
  ext q
  rw [kindProfile_apply, Finsupp.zero_apply]
  have h := Submodule.finrank_le (sector R i q.toMul).toSubmodule
  have hz : Module.finrank ℂ (Generations 0) = 0 := by simp [Generations]
  rw [hz] at h
  omega

#print axioms UnitaryCharacterProfile.independent
#print axioms UnitaryCharacterProfile.internal
#print axioms UnitaryCharacterProfile.profile_apply
#print axioms UnitaryCharacterProfile.total_profile
#print axioms UnitaryCharacterProfile.exists_eigenvector_of_pos
#print axioms UnitaryCharacterProfile.profile_pos_of_eigenvector
#print axioms kindProfile_apply
#print axioms kindProfile_total
#print axioms profiles_totals
#print axioms profiles_compatible
#print axioms mode_at_occupied
#print axioms kindProfile_pos_of_mode
#print axioms support_of_occupied
#print axioms supported_profile_tensors
#print axioms repeated_profile
#print axioms two_occupied_characters
#print axioms zero_profile

end

end GUT.SU5.AuditChargeProfiles
