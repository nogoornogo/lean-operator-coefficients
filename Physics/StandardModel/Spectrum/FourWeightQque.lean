import Physics.StandardModel.Spectrum.TwoConjugationQque
import Physics.StandardModel.Spectrum.QqueLocalTarget

open Math

/-! Actual supported qque from four local dual-index equations. -/

set_option autoImplicit false
namespace GUT.FourWeightQque
noncomputable section

open SU5 SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StructuralConjugationMass ConjugationDualIndex StandardModelLocalOperator
open StandardBranchProtonObstruction StandardModelSlotSupport QqueLocalTarget

variable {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
  (P : Profiles (ChargeLabel H))

def HasTarget : Prop := Matches (RestrictedUnitary.spectrum j rho B hu) P

theorem of_partial_target (ht : ConjugationPartialTarget.HasPartialTarget j rho B hu P) :
    HasTarget j rho B hu P := of_matchesSM _ P ht

theorem quark_profiles_compatible (c : TwoConjugations j)
    (ht : HasTarget j rho B hu P) : P.quark = P.up ∧ P.quark = P.electron := by
  let d := dualIndex j rho B hu
  have hQ : chargeProfile d reducedTenQ = chargeProfile d reducedTenUp := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap31_tenQ] using
      (coeff_permute j rho B hu _ c.quarkUp (reducedTenQ, q)).symm
  have he : chargeProfile d reducedTenQ = chargeProfile d reducedTenElectron := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap04_tenQ] using
      (coeff_permute j rho B hu _ c.quarkElectron (reducedTenQ, q)).symm
  have hm (i : Fin 15) (hi : Monitored i) :
      chargeProfile d (smReducedWeight i) = integral (smCharge P i) :=
    profile_eq _ P ht i hi
  have h0 := hm 0 (Or.inl rfl)
  have h8 := hm 8 (Or.inr (Or.inr (Or.inl rfl)))
  have h14 := hm 14 (Or.inr (Or.inr (Or.inr rfl)))
  rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] at h0
  rw [(smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] at h8
  rw [(smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] at h14
  rw [h0, h8] at hQ
  rw [h0, h14] at he
  exact ⟨integral_injective hQ, integral_injective he⟩

theorem exists_zeroMode (ht : HasTarget j rho B hu P) (i : Fin 15)
    (hi : Monitored i) (q : ChargeLabel H) (hq : 0 < smCharge P i q) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyCharacter (smReducedWeight i, q) g • v := by
  apply UnitaryCharacterSpectrum.exists_eigenvector_of_coeff_ne_zero
    B.radical.toRepresentation (AbelianMassSpectrum.radical_unitary B hu)
  have hp := coefficient_lower_bound _ P (RestrictedUnitary.spectrum_nonneg j rho B hu)
    ht i hi q
  change RestrictedUnitary.spectrum j rho B hu (smReducedWeight i, q) ≠ 0
  omega

theorem exists_supported_qque (hQ : 0 < total P.quark) (c : TwoConjugations j)
    (ht : HasTarget j rho B hu P) :
    ∃ k : Charges (ChargeLabel H),
      SlotsSupported (RestrictedUnitary.spectrum j rho B hu) k qqueOperator ∧
      protonFirstCharacter k = 1 ∧
      ∀ i : Fin 15, Monitored i →
        ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
          ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey k i) g • v := by
  obtain ⟨q, hq⟩ := exists_positive_of_total_pos P.quark hQ
  obtain ⟨hup, he⟩ := quark_profiles_compatible j rho B hu P c ht
  have huq : 0 < P.up q := hup ▸ hq
  have heq : 0 < P.electron q := he ▸ hq
  let k := TwoConjugationQque.qqueCharges q 0 0
  have hs (i : Fin 15) (hi : Monitored i) (hp : 0 < smCharge P i q) :
      RestrictedUnitary.spectrum j rho B hu (smReducedWeight i, q) ≠ 0 := by
    have h := coefficient_lower_bound _ P (RestrictedUnitary.spectrum_nonneg j rho B hu)
      ht i hi q
    omega
  refine ⟨k, (qque_slotsSupported_iff _ k).mpr ⟨?_, ?_, ?_⟩,
    TwoConjugationQque.qqueCharges_neutral q 0 0, ?_⟩
  · exact hs 0 (Or.inl rfl) hq
  · exact hs 8 (Or.inr (Or.inr (Or.inl rfl))) huq
  · exact hs 14 (Or.inr (Or.inr (Or.inr rfl))) heq
  · intro i hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact exists_zeroMode j rho B hu P ht 0 (Or.inl rfl) q hq
    · exact exists_zeroMode j rho B hu P ht 3 (Or.inr (Or.inl rfl)) q hq
    · exact exists_zeroMode j rho B hu P ht 8 (Or.inr (Or.inr (Or.inl rfl))) q huq
    · exact exists_zeroMode j rho B hu P ht 14 (Or.inr (Or.inr (Or.inr rfl))) q heq

theorem slotwise_selection_rule_obstruction (hQ : 0 < total P.quark)
    (c : TwoConjugations j) (ht : HasTarget j rho B hu P) :
    ¬ ForbidsEverySlotSupportedPhysicalDeltaBOneOperator
      (RestrictedUnitary.spectrum j rho B hu) := by
  obtain ⟨k, hs, hn, _⟩ := exists_supported_qque j rho B hu P hQ c ht
  exact not_slotwise_prohibition_of_qque k hs hn

end
end GUT.FourWeightQque
