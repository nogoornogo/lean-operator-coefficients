import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite certificates for a generated Lie subalgebra

Closure against generators suffices when the proposed spanning vectors are
themselves generated. The Jacobi identity supplies closure against iterated
brackets; checking all pairs of proposed basis vectors is unnecessary.
-/

set_option autoImplicit false

namespace Math.GeneratedLieSpan

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lieSpan_le_of_stable (s : Set L) (P : Submodule R L)
    (hmem : s ⊆ P) (hstable : ∀ x ∈ s, ∀ y ∈ P, ⁅x, y⁆ ∈ P) :
    (LieSubalgebra.lieSpan R L s : Submodule R L) ≤ P := by
  intro x hx
  have h : x ∈ P ∧ ∀ y ∈ P, ⁅x, y⁆ ∈ P := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx => exact ⟨hmem hx, hstable x hx⟩
    | zero => exact ⟨P.zero_mem, by simp⟩
    | add x y hx hy ihx ihy =>
      exact ⟨P.add_mem ihx.1 ihy.1, fun z hz => by
        simpa only [add_lie] using P.add_mem (ihx.2 z hz) (ihy.2 z hz)⟩
    | smul a x hx ih =>
      exact ⟨P.smul_mem a ih.1, fun z hz => by
        simpa only [smul_lie] using P.smul_mem a (ih.2 z hz)⟩
    | lie x y hx hy ihx ihy =>
      exact ⟨ihx.2 y ihy.1, fun z hz => by
        rw [lie_lie]
        exact P.sub_mem (ihx.2 _ (ihy.2 z hz)) (ihy.2 _ (ihx.2 z hz))⟩
  exact h.1

theorem span_eq_lieSpan {ι κ : Type*} (v : ι → L) (g : κ → L)
    (hg : ∀ i, g i ∈ Submodule.span R (Set.range v))
    (hv : ∀ i, v i ∈ LieSubalgebra.lieSpan R L (Set.range g))
    (hbracket : ∀ i j, ⁅g i, v j⁆ ∈ Submodule.span R (Set.range v)) :
    Submodule.span R (Set.range v) =
      (LieSubalgebra.lieSpan R L (Set.range g) : Submodule R L) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  · apply lieSpan_le_of_stable
    · rintro _ ⟨i, rfl⟩
      exact hg i
    · rintro _ ⟨i, rfl⟩ y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hbracket i j
      | zero => simp
      | add x y hx hy ihx ihy => simpa only [lie_add] using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa only [lie_smul] using Submodule.smul_mem _ a ih

/-- A well-founded bracket provenance proves actual generated membership. -/
theorem mem_of_provenance {m r : ℕ} (v : Fin m → L) (g : Fin r → L)
    (origin : Fin m → Fin r ⊕ (Fin r × Fin m))
    (h : ∀ i, match origin i with
      | .inl j => v i = g j
      | .inr p => p.2.val < i.val ∧ v i = ⁅g p.1, v p.2⁆) :
    ∀ i, v i ∈ LieSubalgebra.lieSpan R L (Set.range g) := by
  intro i
  induction i using WellFounded.induction (measure Fin.val).wf with
  | h i ih =>
    specialize h i
    cases ho : origin i with
    | inl j =>
      simp only [ho] at h
      rw [h]
      exact LieSubalgebra.subset_lieSpan (Set.mem_range_self j)
    | inr p =>
      simp only [ho] at h
      rw [h.2]
      exact LieSubalgebra.lie_mem _
        (LieSubalgebra.subset_lieSpan (Set.mem_range_self p.1)) (ih p.2 h.1)

end Math.GeneratedLieSpan
