import Physics.StandardModel.Spectrum.ProfileChiralIndex
import GUT.SU6.SelectionRules.StandardBranch.WeylZeroModeSupport

open Math

/-!
# Actual radical support for family-dependent profiles

The finite-dimensional unitary action and its invariant symmetric mass are
arbitrary. Character equality with the dual profile target is an infrared
condition, not an assumption of radical support. Orbit-profile equalities
are separate conditional input here; the UV source must derive them later.
-/

set_option autoImplicit false

namespace GUT.ProfileZeroModeSupport

noncomputable section

open StandardSMCharacterTarget StandardAbelianCharge StandardWeylDualTarget
open InvariantWeylMass StandardModelLocalOperator UnitaryVirtualRealization
open FiniteChargeProfiles StandardBranchProtonObstruction

variable {H : Type*} [CommGroup H]

def radicalRepresentation (R : ActualUnitaryGroupRepresentation (CombinedGroup H))
    (B : SymmetricMass R.rho) : ActualUnitaryGroupRepresentation (CombinedGroup H) where
  V := B.radical.toSubmodule
  rho := B.radical.toRepresentation
  unitary := by intro g v w; exact R.unitary g v w

def spectrum (R : ActualUnitaryGroupRepresentation (CombinedGroup H))
    (B : SymmetricMass R.rho) : ResolvedCharacter (ChargeLabel H) :=
  Finsupp.comapDomain keyMonoidHom (AbelianActualSpectrum.spectrum (radicalRepresentation R B))
    keyMonoidHom_injective.injOn

def HasTarget (R : ActualUnitaryGroupRepresentation (CombinedGroup H))
    (B : SymmetricMass R.rho) (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ) : Prop :=
  PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.CharacterEquivalent
    (lightDualIndex B) (ofCharacter (chiralDifference (targetWithSinglets P s)))

variable (R : ActualUnitaryGroupRepresentation (CombinedGroup H)) (B : SymmetricMass R.rho)
  (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)

theorem spectrum_nonneg (key : ResolvedKey (ChargeLabel H)) : 0 ≤ spectrum R B key :=
  AbelianActualSpectrum.spectrum_nonneg _ _

theorem chiral_spectrum (ht : HasTarget R B P s) :
    chiralDifference (spectrum R B) = chiralDifference (targetWithSinglets P s) := by
  have he : AbelianActualSpectrum.spectrum (radicalRepresentation R B) -
      AbelianActualSpectrum.dual (AbelianActualSpectrum.spectrum (radicalRepresentation R B)) =
      WeylZeroModeSupport.lift (chiralDifference (targetWithSinglets P s)) := by
    apply AbelianActualSpectrum.eval_injective
    intro g
    rw [AbelianActualSpectrum.eval_sub, AbelianActualSpectrum.eval_dual,
      AbelianActualSpectrum.spectrum_eval, AbelianActualSpectrum.spectrum_eval,
      WeylZeroModeSupport.eval_lift]
    have h := ht g
    rw [lightDualIndex, dualIndex_character, Representation.char_dual] at h
    exact h.trans (character_ofCharacter _ g.1.toAdd g.2)
  have hneg (key : ResolvedKey (ChargeLabel H)) :
      AbelianActualSpectrum.dualCharacter (keyMonoidHom key) = keyMonoidHom (-key) := by
    ext g
    exact (keyMonoidHom_neg key g).symm
  ext key
  have h := congrArg (fun p => p (keyMonoidHom key)) he
  simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    spectrum, Finsupp.comapDomain_apply, AbelianActualSpectrum.dual_apply, hneg,
    WeylZeroModeSupport.lift, Finsupp.mapDomain_apply_of_injective keyMonoidHom_injective] using h

theorem profile_le_spectrum (ht : HasTarget R B P s) (i : Fin 15) (q : ChargeLabel H) :
    (smCharge P i q : ℤ) ≤ spectrum R B (smReducedWeight i, q) :=
  coefficient_lower_bound P s _ (spectrum_nonneg R B) (chiral_spectrum R B P s ht) i q

theorem exists_zeroMode (ht : HasTarget R B P s) (i : Fin 15) (q : ChargeLabel H)
    (hq : 0 < smCharge P i q) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyMonoidHom (smReducedWeight i, q) g • v := by
  apply AbelianActualSpectrum.exists_eigenvector_of_coeff_ne_zero (radicalRepresentation R B)
  have hp := profile_le_spectrum R B P s ht i q
  change spectrum R B (smReducedWeight i, q) ≠ 0
  omega

theorem all_occupied_zeroModes (ht : HasTarget R B P s)
    (k : Charges (ChargeLabel H)) (hk : Occupied P k) (i : Fin 15) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, B.radical.toRepresentation g v = keyMonoidHom (smResolvedKey k i) g • v :=
  exists_zeroMode R B P s ht i _ (smCharge_pos_of_occupied P k hk i)

theorem chargesSupported (ht : HasTarget R B P s)
    (k : Charges (ChargeLabel H)) (hk : Occupied P k) : ChargesSupported (spectrum R B) k :=
  chargesSupported_of_occupied P s _ (spectrum_nonneg R B) (chiral_spectrum R B P s ht) k hk

/-- Actual support at all fifteen weights, in addition to the two neutral
operator signatures. No full-gauge tensor or amplitude claim is made. -/
theorem exists_actual_signature_pair (F : Family (ChargeLabel H))
    (ht : HasTarget R B F.profiles s) (hc : OrbitCompatible F.profiles) :
    ∃ Q D : SupportedInvariantOperator (spectrum R B),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, B.radical.toRepresentation g v = keyMonoidHom (smResolvedKey Q.charges i) g • v := by
  obtain ⟨k, hk, hQ, hD⟩ := exists_occupied_trivial_characters F hc
  have hs := chargesSupported R B F.profiles s ht k hk
  refine ⟨supportedQque k hs hQ, supportedDuql k hs hD, rfl, rfl, rfl, ?_⟩
  exact all_occupied_zeroModes R B F.profiles s ht k hk

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator (F : Family (ChargeLabel H))
    (ht : HasTarget R B F.profiles s) (hc : OrbitCompatible F.profiles) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (spectrum R B) := by
  obtain ⟨Q, _, _⟩ := exists_actual_signature_pair R B s F ht hc
  exact Q.not_forbidsEverySupportedPhysicalDeltaBOneOperator

theorem legacy_spectrum (M : StandardWeylMassSource.StandardWeylModel H) :
    spectrum (StandardWeylMassSource.ordinaryFields M.matter) M.mass =
      WeylZeroModeSupport.lightSpectrum M := rfl

theorem legacy_target (M : StandardWeylMassSource.StandardWeylModel H)
    (N : ℕ) (hN : M.generations = (N : ℤ)) :
    HasTarget (StandardWeylMassSource.ordinaryFields M.matter) M.mass
      (FiniteChargeProfiles.pure N M.charges) M.singlets := by
  unfold HasTarget
  rw [targetWithSinglets_pure, ← hN]
  exact M.lightTarget

end

end GUT.ProfileZeroModeSupport
