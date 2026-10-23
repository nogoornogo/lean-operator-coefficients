import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Complex.Basic

/-! Vanishing inputs for arbitrary (possibly nonlinear) coefficient generation. -/
namespace Math.SelectedCoefficientInputs
set_option autoImplicit false

variable {X D E : Type*} [AddCommGroup D] [Module ℂ D]
  [AddCommGroup E] [Module ℂ E]
  (P : D →ₗ[ℂ] E) (F : X → D)

def vanishing : Set X := {x | P (F x) = 0}

@[simp] theorem mem_vanishing (x : X) : x ∈ vanishing P F ↔ P (F x) = 0 := Iff.rfl

theorem vanishing_eq_preimage : vanishing P F = F ⁻¹' (LinearMap.ker P : Set D) := rfl

theorem all_vanish_iff : (∀ x, P (F x) = 0) ↔
    Set.range F ⊆ (LinearMap.ker P : Set D) := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    exact h x
  · intro h x
    exact h ⟨x, rfl⟩

theorem exists_nonzero_iff : (∃ x, P (F x) ≠ 0) ↔
    ¬ Set.range F ⊆ (LinearMap.ker P : Set D) := by
  rw [← all_vanish_iff]
  simp only [not_forall]

theorem zero_selector (h : P = 0) : ∀ x, P (F x) = 0 := by
  intro x
  simp [h]

theorem realized_of_witness (d : D) (hd : P d ≠ 0) (hf : d ∈ Set.range F) :
    ∃ x, P (F x) ≠ 0 := by
  obtain ⟨x, rfl⟩ := hf
  exact ⟨x, hd⟩

theorem exists_nonzero_of_surjective (hF : Function.Surjective F) :
    (∃ x, P (F x) ≠ 0) ↔ P ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩ h
    exact hx (by simp [h])
  · intro hP
    have hd : ∃ d, P d ≠ 0 := by
      by_contra h
      apply hP
      ext d
      simpa using not_exists.mp h d
    obtain ⟨d, hd⟩ := hd
    exact realized_of_witness P F d hd (hF d)

/-- A concrete nonzero selected factor and no cancelling remainder suffice. -/
theorem nonzero_of_factorization (x : X) (a : E) (z : ℂ)
    (h : P (F x) = z • a) (hz : z ≠ 0) (ha : a ≠ 0) : P (F x) ≠ 0 := by
  rw [h]
  exact smul_ne_zero hz ha

end Math.SelectedCoefficientInputs
