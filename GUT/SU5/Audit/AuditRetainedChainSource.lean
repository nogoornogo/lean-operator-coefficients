import Math.Audit.ImportOrigin
import GUT.SU5.SelectionRules.RetainedChainSource
import GUT.SU5.Audit.AuditChargeProfiles

open Math

/-! Legacy generation mixing is preserved by the common-model adapter.
The full spectrum, not only its dual difference, is tested at zero mass.
The existing full-field and invariant-tensor audit remains imported. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Retained SU(5) adapter imports SU(6): {mod}"

namespace GUT.SU5.AuditRetainedChainSource

noncomputable section

open MatterSource RetainedChainSource AuditMatterSource AuditChargeProfiles
open StandardSMCharacterTarget FiniteChargeProfiles FiniteAbelianChargeSectors
open InvariantWeylMass TorusCharacterSource

def mixedModel := model mixingSource (by decide)

theorem mixed_spectrum : mixedModel.lightSpectrum = target (ChargeProfiles.profiles mixingSource) :=
  spectrum_eq mixingSource (by decide)

theorem repeated_coefficient : mixedModel.lightSpectrum (smReducedWeight 9, 0) = 2 := by
  rw [mixed_spectrum, target_apply_smReducedWeight]
  change (ChargeProfiles.kindProfile mixingSource .barFive 0 : ℤ) = 2
  rw [repeated_profile]
  norm_num

theorem distinct_occupied_charges :
    0 < mixedModel.lightSpectrum (smReducedWeight 0, 0) ∧
      0 < mixedModel.lightSpectrum (smReducedWeight 0, Additive.ofMul oddCharacter) := by
  rw [mixed_spectrum, target_apply_smReducedWeight, target_apply_smReducedWeight]
  constructor
  · exact_mod_cast two_occupied_characters.1
  · exact_mod_cast two_occupied_characters.2.1

theorem odd_actual_zero_mode :
    ∃ v : mixedModel.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, mixedModel.mass.radical.toRepresentation g v =
        TorusCharacter.keyCharacter (smReducedWeight 0, Additive.ofMul oddCharacter) g • v :=
  TorusMassSource.exists_zeroMode (joint mixingSource) (joint_unitary mixingSource)
    mixedModel.mass _ 0 (hasTarget mixingSource _) 0 _ two_occupied_characters.2.1

theorem original_residual_action (h : ℤˣ) (x : Space 2) :
    joint mixingSource (1, h) x = (mixingSource h).val.val x := by
  change gauge 2 1 (RetainedChainSource.residual mixingSource h x) = _
  simp [RetainedChainSource.residual]

theorem zero_generations_spectrum {H : Type*} [CommGroup H] (R : OrdinaryAction H 0) :
    TorusMassSource.spectrum (joint R) (joint_unitary R)
      (SymmetricMass.zero (restrict (joint R))) = 0 := by
  rw [retained_spectrum]
  have hp : ChargeProfiles.profiles R = (⟨0, 0, 0, 0, 0⟩ : Profiles (ChargeLabel H)) := by
    simp [ChargeProfiles.profiles, zero_profile]
  rw [hp]
  unfold target
  apply Finset.sum_eq_zero
  intro i _
  fin_cases i <;> simp [smCharge, atWeight, integral]

theorem mixed_obstruction :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      mixedModel.lightSpectrum := mixedModel.selection_rule_obstruction

theorem preserves_given_mass {H : Type*} [CommGroup H] {n : ℕ}
    (R : OrdinaryAction H n) (hn : 0 < n) (B : SymmetricMass (restrict (joint R))) :
    (massModel R hn B).mass.form = B.form := rfl

#print axioms ExplicitMultiplicity.trace_eq_sum_diagonal
#print axioms ExplicitMultiplicity.trace_mix_action
#print axioms UnitaryCharacterSpectrum.profile_eval
#print axioms SymmetricMass.zeroRadicalEquiv
#print axioms CommutingUnitaryActions.combined_jointlyContinuous
#print axioms TorusMatterCharacter.weighted_character
#print axioms ProfileEvaluation.eval_block_target
#print axioms joint_restrict_gauge
#print axioms joint_restrict_residual
#print axioms joint_unitary
#print axioms joint_character
#print axioms kindProfile_eval
#print axioms torus_character
#print axioms hasTarget
#print axioms massModel
#print axioms massModel_mass
#print axioms zero_radical_character
#print axioms zero_radical_spectrum
#print axioms retained_spectrum
#print axioms spectrum_eq
#print axioms RetainedChainSource.selection_rule_obstruction
#print axioms joint_continuous
#print axioms continuousMassModel
#print axioms continuousModel_toModel
#print axioms mixed_spectrum
#print axioms repeated_coefficient
#print axioms distinct_occupied_charges
#print axioms odd_actual_zero_mode
#print axioms original_residual_action
#print axioms zero_generations_spectrum
#print axioms mixed_obstruction
#print axioms preserves_given_mass

end

end GUT.SU5.AuditRetainedChainSource
