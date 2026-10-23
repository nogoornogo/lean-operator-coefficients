import GUT.SU6.SelectionRules.Models.PhysicalWeylMassSource
import GUT.SU6.SelectionRules.StandardBranch.WeylConjugateOperator

open Physics

open Math

/-!
# Actual radical support for the general-cocharacter Weyl model

The infrared target is on the physical weight lattice. Its injective
standard-key embedding permits extracting the same oriented SM sectors from
the actual radical. hypercharge character rigidity and standard charge-orbit bridge, derived from that same target, make the
supported operator invariant. The two index orientations stay distinct.
-/

set_option autoImplicit false

namespace GUT.PhysicalWeylZeroModeSupport

noncomputable section

open PhysicalWeylMassSource StandardSMCharacterTarget StandardAbelianCharge
open StandardWeylDualTarget InvariantWeylMass StandardModelLocalOperator
open StandardPhysicalSpectrumBridge UnitaryVirtualRealization WeylConjugateOperator

variable {H : Type*} [CommGroup H]

def lightRepresentation (M : PhysicalWeylModel H) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) where
  V := M.mass.radical.toSubmodule
  rho := M.mass.radical.toRepresentation
  unitary := by
    intro g v w
    exact (PhysicalMassSpectrumBridge.ordinaryPositiveRepresentation
      M.colorExponent M.weakExponent M.matter).unitary g v w

def lightSpectrum (M : PhysicalWeylModel H) : ResolvedCharacter (ChargeLabel H) :=
  Finsupp.comapDomain keyMonoidHom (AbelianActualSpectrum.spectrum (lightRepresentation M))
    keyMonoidHom_injective.injOn

@[simp] theorem lightSpectrum_apply (M : PhysicalWeylModel H) (key : ResolvedKey (ChargeLabel H)) :
    lightSpectrum M key =
      AbelianActualSpectrum.spectrum (lightRepresentation M) (keyMonoidHom key) := rfl

theorem lightSpectrum_nonneg (M : PhysicalWeylModel H) (key : ResolvedKey (ChargeLabel H)) :
    0 ≤ lightSpectrum M key := AbelianActualSpectrum.spectrum_nonneg _ _

theorem lightSpectrum_chiralDifference (M : PhysicalWeylModel H) :
    chiralDifference (lightSpectrum M) =
      chiralDifference (exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets) := by
  have he : AbelianActualSpectrum.spectrum (lightRepresentation M) -
      AbelianActualSpectrum.dual (AbelianActualSpectrum.spectrum (lightRepresentation M)) =
      WeylZeroModeSupport.lift
        (chiralDifference (exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets)) := by
    apply AbelianActualSpectrum.eval_injective
    intro g
    rw [AbelianActualSpectrum.eval_sub, AbelianActualSpectrum.eval_dual,
      AbelianActualSpectrum.spectrum_eval, AbelianActualSpectrum.spectrum_eval,
      WeylZeroModeSupport.eval_lift]
    have h := M.lightTarget.standard g
    rw [lightDualIndex, dualIndex_character, Representation.char_dual] at h
    exact h.trans (character_ofCharacter _ g.1.toAdd g.2)
  have hneg (key : ResolvedKey (ChargeLabel H)) :
      AbelianActualSpectrum.dualCharacter (keyMonoidHom key) = keyMonoidHom (-key) := by
    ext g
    exact (StandardWeylDualTarget.keyMonoidHom_neg key g).symm
  ext key
  have h := congrArg (fun p => p (keyMonoidHom key)) he
  simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    lightSpectrum_apply, AbelianActualSpectrum.dual_apply, hneg, WeylZeroModeSupport.lift,
    Finsupp.mapDomain_apply_of_injective keyMonoidHom_injective] using h

theorem sm_difference (M : PhysicalWeylModel H) (i : Fin 15) :
    lightSpectrum M (smResolvedKey M.charges i) -
      lightSpectrum M (-smResolvedKey M.charges i) = M.generations := by
  have hp := congrArg (fun p => chargeProfile p (smReducedWeight i)) (lightSpectrum_chiralDifference M)
  rw [chiralDifference_target_chargeProfile] at hp
  have he := congrArg (fun p => p (smCharge M.charges i)) hp
  simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply, dualCharacter_apply] at he
  exact he.trans ((IsExactSMOnlyCoefficientSpectrum.of_resolvedCharacter_eq
    (rfl : exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets = _)).smMultiplicity i)

theorem all_sm_zeroModes (M : PhysicalWeylModel H) (hn : 0 < M.generations) (i : Fin 15) :
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (smResolvedKey M.charges i) g • v := by
  apply AbelianActualSpectrum.exists_eigenvector_of_coeff_ne_zero (lightRepresentation M)
  have he := sm_difference M i
  have hp := lightSpectrum_nonneg M (-smResolvedKey M.charges i)
  change lightSpectrum M (smResolvedKey M.charges i) ≠ 0
  omega

theorem all_conjugate_sm_zeroModes (M : PhysicalWeylModel H) (hn : M.generations < 0) (i : Fin 15) :
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (-smResolvedKey M.charges i) g • v := by
  apply AbelianActualSpectrum.exists_eigenvector_of_coeff_ne_zero (lightRepresentation M)
  have he := sm_difference M i
  have hp := lightSpectrum_nonneg M (smResolvedKey M.charges i)
  change lightSpectrum M (-smResolvedKey M.charges i) ≠ 0
  omega

theorem chargesSupported (M : PhysicalWeylModel H) (hn : 0 < M.generations) :
    ChargesSupported (lightSpectrum M) M.charges := by
  have hp := chiralDifference_target_isPureSMChargeSpectrum M.generations M.charges M.singlets
  rw [← lightSpectrum_chiralDifference M] at hp
  have hs (w : ReducedWeight) (q : ChargeLabel H)
      (he : chargeProfile (chiralDifference (lightSpectrum M)) w = Finsupp.single q M.generations) :
      chargeProfile (lightSpectrum M) w q ≠ 0 := by
    have h := congrArg (fun f => f q) he
    simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply,
      dualCharacter_apply, Finsupp.single_eq_same] at h
    have hpos := lightSpectrum_nonneg M (-(w, q))
    rw [chargeProfile_apply]
    omega
  exact ⟨hs _ _ hp.quark, hs _ _ hp.up, hs _ _ hp.down, hs _ _ hp.lepton, hs _ _ hp.electron⟩

theorem conjugateChargesSupported (M : PhysicalWeylModel H) (hn : M.generations < 0) :
    ChargesSupported (dualCharacter (lightSpectrum M)) M.charges := by
  have hp := chiralDifference_target_isPureSMChargeSpectrum M.generations M.charges M.singlets
  rw [← lightSpectrum_chiralDifference M] at hp
  have hs (w : ReducedWeight) (q : ChargeLabel H)
      (he : chargeProfile (chiralDifference (lightSpectrum M)) w = Finsupp.single q M.generations) :
      chargeProfile (dualCharacter (lightSpectrum M)) w q ≠ 0 := by
    have h := congrArg (fun f => f q) he
    simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply,
      dualCharacter_apply, Finsupp.single_eq_same] at h
    have hpos := lightSpectrum_nonneg M (w, q)
    simp only [chargeProfile_apply, dualCharacter_apply]
    omega
  exact ⟨hs _ _ hp.quark, hs _ _ hp.up, hs _ _ hp.down, hs _ _ hp.lepton, hs _ _ hp.electron⟩

theorem protonFirstCharacter_eq_one (M : PhysicalWeylModel H) :
    FiniteAbelianChargeSectors.protonFirstCharacter M.charges = 1 :=
  FiniteAbelianChargeSectors.protonFirstCharacter_eq_one_of_eq_zero M.charges
    M.proton_functionals_eq_zero.1

def supportedQque (M : PhysicalWeylModel H) (hn : 0 < M.generations) :
    SupportedInvariantOperator (lightSpectrum M) :=
  StandardModelLocalOperator.supportedQque M.charges (chargesSupported M hn) (protonFirstCharacter_eq_one M)

def conjugateQque (M : PhysicalWeylModel H) (hn : M.generations < 0) :
    SupportedConjugateInvariantOperator (lightSpectrum M) where
  charges := M.charges
  supported := conjugateChargesSupported M hn
  operator := .qque
  invariant := by simp [protonFirstCharacter_eq_one M]

theorem exists_invariant_operator_or_conjugate (M : PhysicalWeylModel H) :
    Nonempty (SupportedInvariantOperator (lightSpectrum M)) ∨
      Nonempty (SupportedConjugateInvariantOperator (lightSpectrum M)) := by
  rcases lt_or_gt_of_ne M.generations_ne with hn | hn
  · exact Or.inr ⟨conjugateQque M hn⟩
  · exact Or.inl ⟨supportedQque M hn⟩

theorem not_forbidsBothOrientations (M : PhysicalWeylModel H) :
    ¬ ForbidsBothOrientations (lightSpectrum M) := by
  rintro ⟨hpos, hneg⟩
  rcases exists_invariant_operator_or_conjugate M with h | h
  · obtain ⟨w⟩ := h
    exact w.not_forbidsEverySupportedStandardOperator hpos
  · obtain ⟨w⟩ := h
    exact hneg w.charges w.supported w.operator w.invariant

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (M : PhysicalWeylModel H) (hn : 0 < M.generations) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (lightSpectrum M) :=
  (supportedQque M hn).not_forbidsEverySupportedPhysicalDeltaBOneOperator

end

end GUT.PhysicalWeylZeroModeSupport
