import Math.RepresentationTheory.Characters.UnitaryCharacterProfile
import Math.RepresentationTheory.Characters.AbelianCharacterPolynomial
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Actual finite spectra without a spectator gauge group

Full character eigenspaces supply finite nonnegative multiplicities. Their
evaluation is the actual trace character, so the faithful polynomial model
uniquely determines the spectrum. No topology or finiteness of H is needed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Math.UnitaryCharacterSpectrum

noncomputable section

open AbelianActualSpectrum UnitaryCharacterProfile

variable {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ H E) (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)

def complexCharacter (chi : H →* Circle) : H →* ℂ := Circle.coeHom.comp chi

theorem complexCharacter_injective : Function.Injective (complexCharacter (H := H)) := by
  intro chi psi he
  ext h
  exact congrArg (fun f : H →* ℂ => f h) he

def spectrum : Polynomial H :=
  letI := activeFintype rho hu
  ∑ chi : Active rho,
    Finsupp.single (complexCharacter chi.val) (Module.finrank ℂ (space rho chi.val) : ℤ)

theorem spectrum_nonneg (chi : H →* ℂ) : 0 ≤ spectrum rho hu chi := by
  classical
  let := activeFintype rho hu
  simp only [spectrum, Finsupp.finsetSum_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [Finsupp.single_apply]
  split <;> positivity

/-- Coefficients are full eigenspace dimensions, not chosen multiplicities. -/
theorem spectrum_apply_complexCharacter (chi : H →* Circle) :
    spectrum rho hu (complexCharacter chi) = (profile rho hu chi : ℤ) := by
  classical
  let := activeFintype rho hu
  rw [profile_apply, spectrum, Finsupp.finsetSum_apply]
  by_cases hc : space rho chi = ⊥
  · rw [hc]
    simp only [finrank_bot, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro psi _
    apply Finsupp.single_eq_of_ne
    intro he
    exact psi.property (complexCharacter_injective he ▸ hc)
  · rw [Finset.sum_eq_single (⟨chi, hc⟩ : Active rho)]
    · simp
    · intro psi _ hne
      apply Finsupp.single_eq_of_ne
      intro he
      exact hne (Subtype.ext (complexCharacter_injective he).symm)
    · simp

theorem spectrum_eval (h : H) : eval (spectrum rho hu) h = rho.character h := by
  classical
  let := activeFintype rho hu
  have hm (chi : Active rho) :
      Set.MapsTo (rho h) (space rho chi.val) (space rho chi.val) :=
    (UnitaryCharacterSectors.sector rho chi.val).apply_mem_toSubmodule h
  have he (chi : Active rho) :
      (rho h).restrict (hm chi) = (chi.val h : ℂ) • LinearMap.id := by
    ext v
    exact v.property h
  have hi : DirectSum.IsInternal (fun chi : Active rho => space rho chi.val) :=
    DirectSum.isInternal_ne_bot_iff.mpr (internal rho hu)
  unfold Representation.character
  rw [LinearMap.trace_eq_sum_trace_restrict hi hm]
  simp_rw [he, map_smul, LinearMap.trace_id, smul_eq_mul]
  unfold spectrum eval
  rw [← Finsupp.sum_finsetSum_index]
  · simp [complexCharacter, mul_comm]
    rfl
  · intros; simp
  · intros; simp [add_mul]

theorem profile_eval (h : H) :
    (profile rho hu).sum (fun chi n => (n : ℂ) * (chi h : ℂ)) = rho.character h := by
  classical
  let := activeFintype rho hu
  rw [← spectrum_eval rho hu h]
  unfold profile spectrum eval
  rw [← Finsupp.sum_finsetSum_index, ← Finsupp.sum_finsetSum_index]
  · simp [complexCharacter]
    rfl
  all_goals intros; simp [add_mul]

theorem exists_eigenvector_of_coeff_ne_zero (chi : H →* ℂ)
    (hc : spectrum rho hu chi ≠ 0) :
    ∃ v : E, v ≠ 0 ∧ ∀ h, rho h v = chi h • v := by
  classical
  let := activeFintype rho hu
  simp only [spectrum, Finsupp.finsetSum_apply] at hc
  obtain ⟨psi, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have he : complexCharacter psi.val = chi := by
    by_contra hn
    simp [hn] at hp
  have hd : Module.finrank ℂ (space rho psi.val) ≠ 0 := by
    simpa [he] using hp
  let : Nontrivial (space rho psi.val) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hd)
  obtain ⟨v, hv⟩ := exists_ne (0 : space rho psi.val)
  refine ⟨v, fun hz => hv (Subtype.ext hz), ?_⟩
  intro h
  have hh : (psi.val h : ℂ) = chi h := congrArg (fun f : H →* ℂ => f h) he
  exact (v.property h).trans (congrArg (fun z : ℂ => z • (v : E)) hh)

theorem exists_eigenvector_of_dual_coeff_pos (chi : H →* ℂ)
    (hc : 0 < (spectrum rho hu - dual (spectrum rho hu)) chi) :
    ∃ v : E, v ≠ 0 ∧ ∀ h, rho h v = chi h • v := by
  apply exists_eigenvector_of_coeff_ne_zero rho hu
  have hn := spectrum_nonneg rho hu (dualCharacter chi)
  simp only [Finsupp.sub_apply, dual_apply] at hc
  omega

end

end Math.UnitaryCharacterSpectrum
