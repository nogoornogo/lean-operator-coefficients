import Physics.StandardModel.Spectrum.ConjugationPartialTarget
import Physics.StandardModel.Operators.SlotSupport

open Math

/-! A supported qque signature needs only the Q/up and Q/e conjugations. -/

set_option autoImplicit false
namespace GUT.TwoConjugationQque
noncomputable section

open SU5 SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StructuralConjugationMass ConjugationDualIndex StandardModelLocalOperator
open StandardBranchProtonObstruction StandardModelSlotSupport ConjugationPartialTarget

variable {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
  (P : Profiles (ChargeLabel H))

theorem quark_profiles_compatible (c : TwoConjugations j)
    (ht : HasPartialTarget j rho B hu P) : P.quark = P.up ∧ P.quark = P.electron := by
  let d := dualIndex j rho B hu
  have hQ : chargeProfile d reducedTenQ = chargeProfile d reducedTenUp := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap31_tenQ] using
      (coeff_permute j rho B hu _ c.quarkUp (reducedTenQ, q)).symm
  have he : chargeProfile d reducedTenQ = chargeProfile d reducedTenElectron := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap04_tenQ] using
      (coeff_permute j rho B hu _ c.quarkElectron (reducedTenQ, q)).symm
  have hm (i : Fin 15) : chargeProfile d (smReducedWeight i) = integral (smCharge P i) :=
    SMPartialTarget.profile_eq _ P ht i
  have h0 := hm 0
  have h8 := hm 8
  have h14 := hm 14
  rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] at h0
  rw [(smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] at h8
  rw [(smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] at h14
  rw [h0, h8] at hQ
  rw [h0, h14] at he
  exact ⟨integral_injective hQ, integral_injective he⟩

theorem exists_common_charge (hQ : 0 < total P.quark) (c : TwoConjugations j)
    (ht : HasPartialTarget j rho B hu P) :
    ∃ q, 0 < P.quark q ∧ 0 < P.up q ∧ 0 < P.electron q := by
  obtain ⟨q, hq⟩ := exists_positive_of_total_pos P.quark hQ
  obtain ⟨hu', he⟩ := quark_profiles_compatible j rho B hu P c ht
  exact ⟨q, hq, hu' ▸ hq, he ▸ hq⟩

/-- Uniform species targets at all fifteen weights make the third coordinate
move unnecessary even for the down/lepton profile relation. -/
theorem profiles_compatible (c : TwoConjugations j)
    (ht : HasPartialTarget j rho B hu P) : OrbitCompatible P := by
  obtain ⟨hQ, he⟩ := quark_profiles_compatible j rho B hu P c ht
  refine ⟨hQ, he, ?_⟩
  apply integral_injective
  ext q
  have hm := coeff_permute j rho B hu _ c.quarkUp (smReducedWeight 10, q)
  simp only [permuteKey, swap31_down_lepton] at hm
  change StandardWeylDualTarget.chiralDifference (RestrictedUnitary.spectrum j rho B hu)
      (smReducedWeight 13, q) =
    StandardWeylDualTarget.chiralDifference (RestrictedUnitary.spectrum j rho B hu)
      (smReducedWeight 10, q) at hm
  rw [ht 13 q, ht 10 q] at hm
  exact hm.symm

/-- Spectator charges are arbitrary: neither their equality nor occupancy is
used by the operator-local qque endpoint. -/
def qqueCharges (q d l : ChargeLabel H) : Charges (ChargeLabel H) := ⟨q, q, d, l, q⟩

theorem qqueCharges_neutral (q d l : ChargeLabel H) :
    protonFirstCharacter (qqueCharges q d l) = 1 := by
  apply protonFirstCharacter_eq_one_of_eq_zero
  simp [protonFirst, qqueCharges]

theorem exists_supported_qque (hQ : 0 < total P.quark) (c : TwoConjugations j)
    (ht : HasPartialTarget j rho B hu P) :
    ∃ k : Charges (ChargeLabel H),
      SlotsSupported (RestrictedUnitary.spectrum j rho B hu) k qqueOperator ∧
      protonFirstCharacter k = 1 ∧
      ∀ i : Fin 15, (i = 0 ∨ i = 3 ∨ i = 8 ∨ i = 14) →
        ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
          ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey k i) g • v := by
  obtain ⟨q, hq, hup, he⟩ := exists_common_charge j rho B hu P hQ c ht
  let k := qqueCharges q 0 0
  have hn := RestrictedUnitary.spectrum_nonneg j rho B hu
  have hs (i : Fin 15) (hp : 0 < smCharge P i q) :
      RestrictedUnitary.spectrum j rho B hu (smReducedWeight i, q) ≠ 0 := by
    have h := SMPartialTarget.coefficient_lower_bound _ P hn ht i q
    omega
  refine ⟨k, (qque_slotsSupported_iff _ k).mpr ⟨?_, ?_, ?_⟩,
    qqueCharges_neutral q 0 0, ?_⟩
  · exact hs 0 hq
  · exact hs 8 hup
  · exact hs 14 he
  · intro i hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ConjugationPartialTarget.exists_zeroMode j rho B hu P ht 0 q hq
    · exact ConjugationPartialTarget.exists_zeroMode j rho B hu P ht 3 q hq
    · exact ConjugationPartialTarget.exists_zeroMode j rho B hu P ht 8 q hup
    · exact ConjugationPartialTarget.exists_zeroMode j rho B hu P ht 14 q he

theorem slotwise_selection_rule_obstruction (hQ : 0 < total P.quark)
    (c : TwoConjugations j) (ht : HasPartialTarget j rho B hu P) :
    ¬ ForbidsEverySlotSupportedPhysicalDeltaBOneOperator
      (RestrictedUnitary.spectrum j rho B hu) := by
  obtain ⟨k, hs, hn, _⟩ := exists_supported_qque j rho B hu P hQ c ht
  exact not_slotwise_prohibition_of_qque k hs hn

/-- Retain the exact legacy endpoint when its two unused spectator species
are independently present. No down/lepton equality is required. -/
theorem legacy_selection_rule_obstruction (hQ : 0 < total P.quark)
    (hD : 0 < total P.down) (hL : 0 < total P.lepton)
    (c : TwoConjugations j) (ht : HasPartialTarget j rho B hu P) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (RestrictedUnitary.spectrum j rho B hu) := by
  obtain ⟨q, hq, hup, he⟩ := exists_common_charge j rho B hu P hQ c ht
  obtain ⟨d, hd⟩ := exists_positive_of_total_pos P.down hD
  obtain ⟨l, hl⟩ := exists_positive_of_total_pos P.lepton hL
  have hk : Occupied P (qqueCharges q d l) := ⟨hq, hup, hd, hl, he⟩
  have hs := ConjugationPartialTarget.chargesSupported j rho B hu P ht _ hk
  exact (supportedQque _ hs (qqueCharges_neutral q d l)).not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- The same full-support pair as before, with two actual conjugations.
All fifteen actual light witnesses are retained. -/
theorem exists_actual_signature_pair (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (c : TwoConjugations j) (ht : HasPartialTarget j rho B hu P) :
    ∃ Q D : SupportedInvariantOperator (RestrictedUnitary.spectrum j rho B hu),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey Q.charges i) g • v := by
  obtain ⟨k, hk, hq, hd⟩ := exists_occupied_trivial_characters_of_positive_totals P hQ hD
    (profiles_compatible j rho B hu P c ht)
  have hs := ConjugationPartialTarget.chargesSupported j rho B hu P ht k hk
  refine ⟨supportedQque k hs hq, supportedDuql k hs hd, rfl, rfl, rfl, ?_⟩
  intro i
  exact ConjugationPartialTarget.exists_zeroMode j rho B hu P ht i _
    (smCharge_pos_of_occupied P k hk i)

theorem selection_rule_obstruction (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (c : TwoConjugations j) (ht : HasPartialTarget j rho B hu P) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (RestrictedUnitary.spectrum j rho B hu) := by
  obtain ⟨Q, _, _⟩ := exists_actual_signature_pair j rho B hu P hQ hD c ht
  exact Q.not_forbidsEverySupportedPhysicalDeltaBOneOperator

end
end GUT.TwoConjugationQque
