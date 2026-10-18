import Physics.FieldTheory.Mass.ResidualMassIndex
import Math.RepresentationTheory.Characters.PositiveCharacterQuotient
import Math.RepresentationTheory.Decomposition.FiniteIrreducibleQuotient

open Math

/-!
# Positive residual indices yield actual split light quotients

The negative contribution is the actual dual of the opposite-weight space.
Thus a positive target constituent cannot disappear from the light sector.
-/

set_option autoImplicit false

namespace GUT.ResidualLightQuotient

noncomputable section

open Representation ResidualWeightSpace ResidualWeightCharacter
open SplitRepresentationProjection

variable {T H V P R : Type*} [CommGroup T] [Group H] [Fintype H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]
  [AddCommGroup R] [Module ℂ R] [FiniteDimensional ℂ R]

theorem exists_split_of_index_eq (light : Representation ℂ (T × H) V)
    (chi : T →* Circle) (target : Representation ℂ H P)
    (tau : Representation ℂ H R) [IsIrreducible tau]
    (ht : ∀ h, index light chi h = target.character h)
    (f : IntertwiningMap target tau) (hf : f ≠ 0) :
    Nonempty (Split (representation light chi) tau) := by
  have hc : ∀ h, (representation light chi).character h =
      (representation light chi⁻¹).dual.character h + target.character h := by
    intro h
    have he := ht h
    unfold index at he
    linear_combination he
  obtain ⟨p, hp⟩ :=
    PositiveCharacterQuotient.exists_surjective_of_character_add_of_nonzero
      (representation light chi) (representation light chi⁻¹).dual target tau hc f hf
  obtain ⟨S, _⟩ := FiniteIrreducibleQuotient.exists_split _ _ p hp
  exact ⟨S⟩

/-- A single nonzero target supplies one common irreducible quotient at every
weight whose dual index equals that target. The constituent is not an input. -/
theorem exists_common_quotient (light : Representation ℂ (T × H) V)
    (target : Representation ℂ H P) [Nontrivial P] :
    ∃ S : Subrepresentation target, IsIrreducible S.toRepresentation ∧
      Nontrivial S.toSubmodule ∧ ∀ chi : T →* Circle,
        (∀ h, index light chi h = target.character h) →
          Nonempty (Split (representation light chi) S.toRepresentation) := by
  obtain ⟨S, hi, hn, f, hf⟩ := FiniteIrreducibleQuotient.exists_irreducible_quotient target
  let : IsIrreducible S.toRepresentation := hi
  let : Nontrivial S.toSubmodule := hn
  have hfn : f ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
    obtain ⟨y, hy⟩ := hf x
    apply hx
    simpa [he] using hy.symm
  exact ⟨S, hi, hn, fun chi ht => exists_split_of_index_eq light chi target
    S.toRepresentation ht f hfn⟩

end
end GUT.ResidualLightQuotient
