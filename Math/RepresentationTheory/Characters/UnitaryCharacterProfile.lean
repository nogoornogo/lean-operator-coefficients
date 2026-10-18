import Math.RepresentationTheory.Characters.UnitaryCharacterSectors
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Finsupp.Basic

/-!
# Natural finite multiplicities of unitary Abelian character sectors

The acting group need not be finite or topological. The profile counts full
character eigenspaces and its total is the dimension of the representation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Math.UnitaryCharacterProfile

noncomputable section

variable {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ H E) (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)

local instance : DecidableEq (H →* Circle) := Classical.decEq _

abbrev space (chi : H →* Circle) : Submodule ℂ E :=
  (UnitaryCharacterSectors.sector rho chi).toSubmodule

omit [FiniteDimensional ℂ E] in
include hu in
theorem independent : iSupIndep (space rho) := by
  apply OrthogonalFamily.independent
  intro chi psi hne v w
  exact UnitaryCharacterSectors.distinct_sectors_orthogonal rho hu chi psi hne v w v.property w.property

include hu in
theorem internal : DirectSum.IsInternal (space rho) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (independent rho hu)
    (UnitaryCharacterSectors.iSup_sector_eq_top rho hu)

abbrev Active := {chi : H →* Circle // space rho chi ≠ ⊥}

@[instance_reducible] def activeFintype : Fintype (Active rho) :=
  (independent rho hu).fintypeNeBotOfFiniteDimensional

def profile : (H →* Circle) →₀ ℕ :=
  letI := activeFintype rho hu
  ∑ chi : Active rho, Finsupp.single chi.val (Module.finrank ℂ (space rho chi.val))

@[simp] theorem profile_apply (chi : H →* Circle) :
    profile rho hu chi = Module.finrank ℂ (space rho chi) := by
  classical
  let := activeFintype rho hu
  rw [profile, Finsupp.finsetSum_apply]
  by_cases hc : space rho chi = ⊥
  · rw [hc]
    simp only [finrank_bot]
    apply Finset.sum_eq_zero
    intro psi _
    apply Finsupp.single_eq_of_ne
    intro he
    exact psi.property (he ▸ hc)
  · rw [Finset.sum_eq_single (⟨chi, hc⟩ : Active rho)]
    · simp
    · intro psi _ hne
      apply Finsupp.single_eq_of_ne
      intro he
      exact hne (Subtype.ext he.symm)
    · simp

theorem total_profile : (profile rho hu).sum (fun _ n => n) = Module.finrank ℂ E := by
  classical
  let := activeFintype rho hu
  have hi : DirectSum.IsInternal (fun chi : Active rho => space rho chi.val) :=
    DirectSum.isInternal_ne_bot_iff.mpr (internal rho hu)
  have hd := (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hi).finrank_eq
  rw [Module.finrank_directSum] at hd
  rw [profile, ← Finsupp.sum_finsetSum_index]
  · simpa using hd
  · simp
  · simp

theorem exists_eigenvector_of_pos (chi : H →* Circle) (hp : 0 < profile rho hu chi) :
    ∃ v : E, v ≠ 0 ∧ ∀ h, rho h v = (chi h : ℂ) • v := by
  rw [profile_apply] at hp
  let : Nontrivial (space rho chi) := Module.nontrivial_of_finrank_pos hp
  obtain ⟨v, hv⟩ := exists_ne (0 : space rho chi)
  exact ⟨v, fun he => hv (Subtype.ext he), v.property⟩

theorem profile_pos_of_eigenvector (chi : H →* Circle) (v : E) (hv : v ≠ 0)
    (he : ∀ h, rho h v = (chi h : ℂ) • v) : 0 < profile rho hu chi := by
  rw [profile_apply]
  let : Nontrivial (space rho chi) := Submodule.nontrivial_iff_ne_bot.mpr
    (UnitaryCharacterSectors.eigenvector_sector_nonzero rho chi v hv he)
  exact Module.finrank_pos

end

end Math.UnitaryCharacterProfile
