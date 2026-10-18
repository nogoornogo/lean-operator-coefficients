import GUT.SU6.SelectionRules.StandardBranch.StandardWeylMassSource
import Math.RepresentationTheory.Characters.UnitaryCharacterSpectrum

open Math

/-!
# Nonnegative character multiplicities of actual unitary Abelian actions

Reuse the full-character-sector decomposition with a trivial spectator
SU(6) action. No continuity or finiteness assumption on the Abelian group is
needed. The resulting coefficients count actual eigenspace dimensions.
-/

set_option autoImplicit false

namespace GUT.AbelianActualSpectrum

open Math.AbelianActualSpectrum
noncomputable section

open UnitaryVirtualRealization FiniteAbelianChargeSectors
open FiniteSemisimpleDecomposition

variable {G : Type*} [CommGroup G]

def spectator (R : ActualUnitaryGroupRepresentation G) :
    ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation where
  V := R.V
  rho := Representation.trivial ℂ _ R.V
  unitary := by intro g x y; rfl
  continuous_action := continuous_snd

def action (R : ActualUnitaryGroupRepresentation G) : CommutingAction G (spectator R) where
  rho := R.rho
  unitary := R.unitary
  commutes := by
    intro h g
    change R.rho h * 1 = 1 * R.rho h
    simp

def decomposition (R : ActualUnitaryGroupRepresentation G) : Decomposition (action R).rho :=
  (exists_decomposition _ (action R).isSemisimpleRepresentation).some

abbrev SectorIndex (R : ActualUnitaryGroupRepresentation G) :=
  Fin ((action R).NumberOfActiveCharacters (decomposition R))

def sector (R : ActualUnitaryGroupRepresentation G) (i : SectorIndex R) : Submodule ℂ R.V :=
  (action R).indexedCharacterSubmodule (decomposition R) i

def character (R : ActualUnitaryGroupRepresentation G) (i : SectorIndex R) : G →* ℂ :=
  StandardSMCharacterTarget.circleCoeMonoidHom.comp
    ((action R).indexedCharacter (decomposition R) i)

theorem sector_action (R : ActualUnitaryGroupRepresentation G) (i : SectorIndex R)
    (v : sector R i) (g : G) : R.rho g v = character R i g • (v : R.V) :=
  v.property g

def spectrum (R : ActualUnitaryGroupRepresentation G) : Polynomial G :=
  ∑ i : SectorIndex R, Finsupp.single (character R i) (Module.finrank ℂ (sector R i) : ℤ)

theorem spectrum_nonneg (R : ActualUnitaryGroupRepresentation G) (chi : G →* ℂ) :
    0 ≤ spectrum R chi := by
  classical
  simp only [spectrum, Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [Finsupp.single_apply]
  split <;> positivity

theorem spectrum_eval (R : ActualUnitaryGroupRepresentation G) (g : G) :
    eval (spectrum R) g = R.rho.character g := by
  classical
  have hm (i : SectorIndex R) : Set.MapsTo (R.rho g) (sector R i) (sector R i) := by
    intro v hv
    rw [sector_action R i ⟨v, hv⟩ g]
    exact (sector R i).smul_mem _ hv
  have he (i : SectorIndex R) :
      (R.rho g).restrict (hm i) = character R i g • LinearMap.id := by
    ext v
    exact sector_action R i v g
  unfold Representation.character
  have hInternal : DirectSum.IsInternal (sector R) :=
    (action R).indexedCharacterSubmodule_isInternal (decomposition R)
  rw [LinearMap.trace_eq_sum_trace_restrict hInternal hm]
  simp_rw [he, map_smul, LinearMap.trace_id, smul_eq_mul]
  unfold spectrum eval
  rw [← Finsupp.sum_finsetSum_index]
  · simp [mul_comm]
  · intro chi
    simp
  · intro chi a b
    simp [add_mul]

/-- The legacy spectator construction computes the same full spectrum as
the group-independent eigenspace construction. -/
theorem spectrum_eq_unitaryCharacterSpectrum (R : ActualUnitaryGroupRepresentation G) :
    spectrum R = UnitaryCharacterSpectrum.spectrum R.rho R.unitary := by
  apply eval_injective
  intro g
  rw [spectrum_eval, UnitaryCharacterSpectrum.spectrum_eval]

theorem exists_eigenvector_of_coeff_ne_zero (R : ActualUnitaryGroupRepresentation G)
    (chi : G →* ℂ) (h : spectrum R chi ≠ 0) :
    ∃ v : R.V, v ≠ 0 ∧ ∀ g, R.rho g v = chi g • v := by
  classical
  simp only [spectrum, Finsupp.finsetSum_apply] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hchi : character R i = chi := by
    by_contra hn
    simp [hn] at hi
  have hd : Module.finrank ℂ (sector R i) ≠ 0 := by
    simpa [hchi] using hi
  have : Nontrivial (sector R i) := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hd)
  obtain ⟨v, hv⟩ := exists_ne (0 : sector R i)
  refine ⟨v, ?_, ?_⟩
  · intro he
    exact hv (Subtype.ext he)
  · intro g
    rw [sector_action, hchi]

/-- Positivity fixes the orientation that nonzero virtual support cannot fix. -/
theorem exists_eigenvector_of_dual_coeff_pos (R : ActualUnitaryGroupRepresentation G)
    (chi : G →* ℂ) (h : 0 < (spectrum R - dual (spectrum R)) chi) :
    ∃ v : R.V, v ≠ 0 ∧ ∀ g, R.rho g v = chi g • v := by
  apply exists_eigenvector_of_coeff_ne_zero
  have hn := spectrum_nonneg R (dualCharacter chi)
  simp only [Finsupp.sub_apply, dual_apply] at h
  omega

end

end GUT.AbelianActualSpectrum
