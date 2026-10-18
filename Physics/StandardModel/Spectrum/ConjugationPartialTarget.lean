import Physics.StandardModel.Spectrum.ConjugationDualIndex
import Physics.StandardModel.Spectrum.SMPartialTarget

open Math

/-! Supported neutral signatures require only the SM-weight part of the
actual light dual index, not a global SM-plus-singlet target. -/

set_option autoImplicit false
namespace GUT.ConjugationPartialTarget
noncomputable section

open SU5 SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StructuralConjugationMass ConjugationDualIndex StandardModelLocalOperator
open StandardBranchProtonObstruction

variable {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
  (P : Profiles (ChargeLabel H))

def HasPartialTarget : Prop := SMPartialTarget.MatchesSM (RestrictedUnitary.spectrum j rho B hu) P

theorem of_full_target (s : ChargeLabel H →₀ ℤ) (ht : HasTarget j rho B P s) :
    HasPartialTarget j rho B hu P :=
  SMPartialTarget.of_full_target _ P s (RestrictedUnitary.chiral_spectrum j rho B P s hu ht)

theorem profiles_compatible (c : ThreeConjugations j) (ht : HasPartialTarget j rho B hu P) :
    OrbitCompatible P := by
  let d := dualIndex j rho B hu
  have hQ : chargeProfile d reducedTenQ = chargeProfile d reducedTenUp := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap31_tenQ] using
      (coeff_permute j rho B hu _ c.quarkUp (reducedTenQ, q)).symm
  have he : chargeProfile d reducedTenQ = chargeProfile d reducedTenElectron := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap04_tenQ] using
      (coeff_permute j rho B hu _ c.quarkElectron (reducedTenQ, q)).symm
  have hd : chargeProfile d reducedBarFiveDown = chargeProfile d reducedBarFiveLepton := by
    ext q
    simpa only [chargeProfile_apply, permuteKey, permuteReducedWeight_swap03_barFiveDown] using
      (coeff_permute j rho B hu _ c.downLepton (reducedBarFiveDown, q)).symm
  have hm (i : Fin 15) : chargeProfile d (smReducedWeight i) = integral (smCharge P i) :=
    SMPartialTarget.profile_eq _ P ht i
  have h0 := hm 0
  have h8 := hm 8
  have h9 := hm 9
  have h13 := hm 13
  have h14 := hm 14
  rw [(smReducedWeight_eq_reducedTenQ_iff 0).mpr rfl] at h0
  rw [(smReducedWeight_eq_reducedTenUp_iff 8).mpr rfl] at h8
  rw [(smReducedWeight_eq_reducedBarFiveDown_iff 9).mpr rfl] at h9
  rw [(smReducedWeight_eq_reducedBarFiveLepton_iff 13).mpr rfl] at h13
  rw [(smReducedWeight_eq_reducedTenElectron_iff 14).mpr rfl] at h14
  rw [h0, h8] at hQ
  rw [h0, h14] at he
  rw [h9, h13] at hd
  exact ⟨integral_injective hQ, integral_injective he, integral_injective hd⟩

theorem exists_zeroMode (ht : HasPartialTarget j rho B hu P) (i : Fin 15) (q : ChargeLabel H)
    (hq : 0 < smCharge P i q) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyCharacter (smReducedWeight i, q) g • v := by
  apply UnitaryCharacterSpectrum.exists_eigenvector_of_coeff_ne_zero
    B.radical.toRepresentation (AbelianMassSpectrum.radical_unitary B hu)
  have hp := SMPartialTarget.coefficient_lower_bound _ P
    (RestrictedUnitary.spectrum_nonneg j rho B hu) ht i q
  change RestrictedUnitary.spectrum j rho B hu (smReducedWeight i, q) ≠ 0
  omega

theorem chargesSupported (ht : HasPartialTarget j rho B hu P)
    (k : Charges (ChargeLabel H)) (hk : Occupied P k) :
    ChargesSupported (RestrictedUnitary.spectrum j rho B hu) k :=
  SMPartialTarget.chargesSupported_of_occupied _ P
    (RestrictedUnitary.spectrum_nonneg j rho B hu) ht k hk

theorem exists_actual_signature_pair (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (c : ThreeConjugations j) (ht : HasPartialTarget j rho B hu P) :
    ∃ Q D : SupportedInvariantOperator (RestrictedUnitary.spectrum j rho B hu),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, B.radical.toRepresentation g v = keyCharacter (smResolvedKey Q.charges i) g • v := by
  obtain ⟨k, hk, hq, hd⟩ := exists_occupied_trivial_characters_of_positive_totals P hQ hD
    (profiles_compatible j rho B hu P c ht)
  have hs := chargesSupported j rho B hu P ht k hk
  refine ⟨supportedQque k hs hq, supportedDuql k hs hd, rfl, rfl, rfl, ?_⟩
  intro i
  exact exists_zeroMode j rho B hu P ht i _ (smCharge_pos_of_occupied P k hk i)

theorem selection_rule_obstruction (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (c : ThreeConjugations j) (ht : HasPartialTarget j rho B hu P) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (RestrictedUnitary.spectrum j rho B hu) := by
  obtain ⟨Q, _, _⟩ := exists_actual_signature_pair j rho B hu P hQ hD c ht
  exact Q.not_forbidsEverySupportedPhysicalDeltaBOneOperator

end
end GUT.ConjugationPartialTarget
