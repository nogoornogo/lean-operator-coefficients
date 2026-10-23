import GUT.SU6.SelectionRules.Models.AbelianActualSpectrum
import GUT.SU6.SelectionRules.StandardBranch.StandardWeylSupportedOperator

open Physics

open Math

/-!
# From the dual index to actual radical support

Actual multiplicities are nonnegative. A positive generation index therefore
forces every oriented SM weight/charge sector to contain a nonzero massless
vector. The operator endpoints use this radical support, not UV support.
Negative indices instead force the conjugate sectors; they are not silently
treated as positive generations.
-/

set_option autoImplicit false

namespace GUT.WeylZeroModeSupport

noncomputable section

open StandardWeylMassSource StandardSMCharacterTarget StandardAbelianCharge
open StandardWeylDualTarget InvariantWeylMass StandardModelLocalOperator
open UnitaryVirtualRealization StandardPhysicalSpectrumBridge

variable {H : Type*} [CommGroup H]

def lift (p : ResolvedCharacter (ChargeLabel H)) :
    AbelianActualSpectrum.Polynomial (CombinedGroup H) := Finsupp.mapDomain keyMonoidHom p

theorem eval_lift (p : ResolvedCharacter (ChargeLabel H)) (g : CombinedGroup H) :
    AbelianActualSpectrum.eval (lift p) g = eval p g.1.toAdd g.2 := by
  classical
  unfold AbelianActualSpectrum.eval lift
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; simp [add_mul]

def lightRepresentation (M : StandardWeylModel H) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) where
  V := M.mass.radical.toSubmodule
  rho := M.mass.radical.toRepresentation
  unitary := by
    intro g v w
    exact (ordinaryFields M.matter).unitary g v w

/-- The actual multiplicities at the integral SM lattice keys. No claim
that arbitrary Abelian characters are all integral lattice keys is needed. -/
def lightSpectrum (M : StandardWeylModel H) : ResolvedCharacter (ChargeLabel H) :=
  Finsupp.comapDomain keyMonoidHom (AbelianActualSpectrum.spectrum (lightRepresentation M))
    keyMonoidHom_injective.injOn

@[simp] theorem lightSpectrum_apply (M : StandardWeylModel H)
    (key : ResolvedKey (ChargeLabel H)) :
    lightSpectrum M key =
      AbelianActualSpectrum.spectrum (lightRepresentation M) (keyMonoidHom key) := rfl

theorem lightSpectrum_nonneg (M : StandardWeylModel H) (key : ResolvedKey (ChargeLabel H)) :
    0 ≤ lightSpectrum M key := AbelianActualSpectrum.spectrum_nonneg _ _

theorem light_dual_spectrum (M : StandardWeylModel H) :
    AbelianActualSpectrum.spectrum (lightRepresentation M) -
      AbelianActualSpectrum.dual (AbelianActualSpectrum.spectrum (lightRepresentation M)) =
      lift (chiralDifference
        (exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets)) := by
  apply AbelianActualSpectrum.eval_injective
  intro g
  rw [AbelianActualSpectrum.eval_sub, AbelianActualSpectrum.eval_dual,
    AbelianActualSpectrum.spectrum_eval, AbelianActualSpectrum.spectrum_eval, eval_lift]
  have h := M.lightTarget g
  rw [lightDualIndex, dualIndex_character, Representation.char_dual] at h
  exact h.trans (character_ofCharacter _ g.1.toAdd g.2)

theorem lightSpectrum_chiralDifference (M : StandardWeylModel H) :
    chiralDifference (lightSpectrum M) =
      chiralDifference (exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets) := by
  have hneg (key : ResolvedKey (ChargeLabel H)) :
      AbelianActualSpectrum.dualCharacter (keyMonoidHom key) = keyMonoidHom (-key) := by
    ext g
    exact (keyMonoidHom_neg key g).symm
  ext key
  have h := congrArg (fun p => p (keyMonoidHom key)) (light_dual_spectrum M)
  simpa only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    lightSpectrum_apply, AbelianActualSpectrum.dual_apply, hneg, lift,
    Finsupp.mapDomain_apply_of_injective keyMonoidHom_injective] using h

theorem lightSpectrum_sm_difference (M : StandardWeylModel H) (i : Fin 15) :
    lightSpectrum M (smResolvedKey M.charges i) -
      lightSpectrum M (-smResolvedKey M.charges i) = M.generations := by
  have hp := congrArg (fun p => chargeProfile p (smReducedWeight i))
    (lightSpectrum_chiralDifference M)
  rw [chiralDifference_target_chargeProfile] at hp
  have h := congrArg (fun p => p (smCharge M.charges i)) hp
  simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply,
    dualCharacter_apply] at h
  have ht := (IsExactSMOnlyCoefficientSpectrum.of_resolvedCharacter_eq
    (rfl : exactSMWithSingletsResolvedCharacter M.generations M.charges M.singlets = _)).smMultiplicity i
  exact h.trans ht

theorem lightSpectrum_sm_pos (M : StandardWeylModel H) (hn : 0 < M.generations)
    (i : Fin 15) : 0 < lightSpectrum M (smResolvedKey M.charges i) := by
  have h := lightSpectrum_sm_difference M i
  have hp := lightSpectrum_nonneg M (-smResolvedKey M.charges i)
  omega

theorem lightSpectrum_conjugate_sm_pos (M : StandardWeylModel H) (hn : M.generations < 0)
    (i : Fin 15) : 0 < lightSpectrum M (-smResolvedKey M.charges i) := by
  have h := lightSpectrum_sm_difference M i
  have hp := lightSpectrum_nonneg M (smResolvedKey M.charges i)
  omega

/-- A genuine nonzero vector in the mass radical, with both gauge weight
and residual character specified. -/
theorem exists_zeroMode (M : StandardWeylModel H) (key : ResolvedKey (ChargeLabel H))
    (h : lightSpectrum M key ≠ 0) :
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom key g • v :=
  AbelianActualSpectrum.exists_eigenvector_of_coeff_ne_zero (lightRepresentation M) _ h

theorem all_sm_zeroModes (M : StandardWeylModel H) (hn : 0 < M.generations) (i : Fin 15) :
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (smResolvedKey M.charges i) g • v :=
  exists_zeroMode M _ (ne_of_gt (lightSpectrum_sm_pos M hn i))

theorem all_conjugate_sm_zeroModes (M : StandardWeylModel H) (hn : M.generations < 0)
    (i : Fin 15) :
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v =
        keyMonoidHom (-smResolvedKey M.charges i) g • v :=
  exists_zeroMode M _ (ne_of_gt (lightSpectrum_conjugate_sm_pos M hn i))

theorem chargesSupported (M : StandardWeylModel H) (hn : 0 < M.generations) :
    ChargesSupported (lightSpectrum M) M.charges := by
  have hp := chiralDifference_target_isPureSMChargeSpectrum
    M.generations M.charges M.singlets
  rw [← lightSpectrum_chiralDifference M] at hp
  have hsupport (w : ReducedWeight) (q : ChargeLabel H)
      (he : chargeProfile (chiralDifference (lightSpectrum M)) w =
        Finsupp.single q M.generations) : chargeProfile (lightSpectrum M) w q ≠ 0 := by
    have h := congrArg (fun f => f q) he
    simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply,
      dualCharacter_apply, Finsupp.single_eq_same] at h
    have hpos := lightSpectrum_nonneg M (-(w, q))
    rw [chargeProfile_apply]
    omega
  exact ⟨hsupport _ _ hp.quark, hsupport _ _ hp.up, hsupport _ _ hp.down,
    hsupport _ _ hp.lepton, hsupport _ _ hp.electron⟩

def supportedQque (M : StandardWeylModel H) (hn : 0 < M.generations) :
    SupportedInvariantOperator (lightSpectrum M) :=
  StandardModelLocalOperator.supportedQque M.charges (chargesSupported M hn)
    (StandardWeylSupportedOperator.protonFirstCharacter_eq_one M)

def supportedDuql (M : StandardWeylModel H) (hn : 0 < M.generations) :
    SupportedInvariantOperator (lightSpectrum M) :=
  StandardModelLocalOperator.supportedDuql M.charges (chargesSupported M hn)
    (StandardWeylSupportedOperator.protonSecondCharacter_eq_one M)

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (M : StandardWeylModel H) (hn : 0 < M.generations) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (lightSpectrum M) :=
  (supportedQque M hn).not_forbidsEverySupportedPhysicalDeltaBOneOperator

end

end GUT.WeylZeroModeSupport
