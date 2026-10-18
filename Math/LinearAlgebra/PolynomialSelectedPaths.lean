import Math.LinearAlgebra.WeightedSelectedPaths
import Mathlib.Algebra.MvPolynomial.Funext

/-! Nonvanishing polynomial generation, without independently isolating paths. -/
namespace Math.PolynomialSelectedPaths
set_option autoImplicit false
noncomputable section
open MvPolynomial

variable {I S D : Type*} [Fintype I] [AddCommGroup D] [Module ℂ D]
  (P : D →ₗ[ℂ] ℂ) (paths : I → D) (p : I → MvPolynomial S ℂ)

def selectedPolynomial : MvPolynomial S ℂ := ∑ i, C (P (paths i)) * p i

theorem eval_selected (x : S → ℂ) :
    eval x (selectedPolynomial P paths p) =
      P (WeightedSelectedPaths.synthesis paths (fun y i => eval y (p i)) x) := by
  simp [selectedPolynomial, WeightedSelectedPaths.selected, mul_comm, smul_eq_mul]

theorem coefficient (d : S →₀ ℕ) :
    (selectedPolynomial P paths p).coeff d = ∑ i, P (paths i) * (p i).coeff d := by
  simp [selectedPolynomial, coeff_C_mul]

/-- A product of infinite coordinate sets detects every nonzero polynomial. -/
theorem exists_nonzero_on_box_iff (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s,
      P (WeightedSelectedPaths.synthesis paths (fun y i => eval y (p i)) x) ≠ 0) ↔
    selectedPolynomial P paths p ≠ 0 := by
  constructor
  · rintro ⟨x, _, hx⟩ hz
    rw [← eval_selected, hz, map_zero] at hx
    exact hx rfl
  · intro hp
    by_contra h
    apply hp
    apply MvPolynomial.funext_set s hs
    intro x hx
    have he : P (WeightedSelectedPaths.synthesis paths (fun y i => eval y (p i)) x) = 0 := by
      by_contra hn
      exact h ⟨x, hx, hn⟩
    simpa only [eval_selected, map_zero] using he

theorem exists_nonzero_on_box_iff_coefficient
    (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s,
      P (WeightedSelectedPaths.synthesis paths (fun y i => eval y (p i)) x) ≠ 0) ↔
    ∃ d : S →₀ ℕ, (∑ i, P (paths i) * (p i).coeff d) ≠ 0 := by
  rw [exists_nonzero_on_box_iff P paths p s hs]
  simp only [ne_eq, MvPolynomial.ext_iff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    not_forall, coefficient]

theorem exists_nonzero_iff_coefficient :
    (∃ x, P (WeightedSelectedPaths.synthesis paths (fun y i => eval y (p i)) x) ≠ 0) ↔
    ∃ d : S →₀ ℕ, (∑ i, P (paths i) * (p i).coeff d) ≠ 0 := by
  simpa using exists_nonzero_on_box_iff_coefficient P paths p
    (fun _ => Set.univ) (fun _ => Set.infinite_univ)

/-- Distinct monomials prevent identically cancelling selected paths. -/
theorem monomial_coefficient (degrees : I → S →₀ ℕ)
    (hd : Function.Injective degrees) (i : I) :
    (selectedPolynomial P paths (fun j => monomial (degrees j) 1)).coeff (degrees i) =
      P (paths i) := by
  classical
  rw [coefficient, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hdeg : degrees j ≠ degrees i := fun h => hji (hd h)
    simp [coeff_monomial, hdeg]
  · simp

theorem exists_nonzero_monomials_iff_path (degrees : I → S →₀ ℕ)
    (hd : Function.Injective degrees) (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s, P (WeightedSelectedPaths.synthesis paths
      (fun y i => eval y (monomial (degrees i) 1)) x) ≠ 0) ↔
    ∃ i, P (paths i) ≠ 0 := by
  rw [exists_nonzero_on_box_iff]
  constructor
  · intro h
    by_contra hn
    have hz : ∀ i, P (paths i) = 0 := by simpa using hn
    exact h (by simp [selectedPolynomial, hz])
  · rintro ⟨i, hi⟩ hz
    have hc := congrArg (fun q : MvPolynomial S ℂ => q.coeff (degrees i)) hz
    rw [monomial_coefficient P paths degrees hd i, AddMonoidAlgebra.coeff_zero] at hc
    exact hi hc
  · exact hs

variable (Q : D →ₗ[ℂ] (ℂ × ℂ))

theorem pair_exists_nonzero_on_box_iff_coefficient
    (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s,
      Q (WeightedSelectedPaths.synthesis paths (fun y i => eval y (p i)) x) ≠ 0) ↔
    ∃ d : S →₀ ℕ, (∑ i, (Q (paths i)).1 * (p i).coeff d) ≠ 0 ∨
      (∑ i, (Q (paths i)).2 * (p i).coeff d) ≠ 0 := by
  have hB := exists_nonzero_on_box_iff_coefficient
    ((LinearMap.fst ℂ ℂ ℂ).comp Q) paths p s hs
  have hW := exists_nonzero_on_box_iff_coefficient
    ((LinearMap.snd ℂ ℂ ℂ).comp Q) paths p s hs
  simpa only [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or,
    and_or_left, exists_or] using hB.or hW

theorem pair_exists_nonzero_monomials_iff_path (degrees : I → S →₀ ℕ)
    (hd : Function.Injective degrees) (s : S → Set ℂ) (hs : ∀ j, (s j).Infinite) :
    (∃ x ∈ Set.pi Set.univ s, Q (WeightedSelectedPaths.synthesis paths
      (fun y i => eval y (monomial (degrees i) 1)) x) ≠ 0) ↔
    ∃ i, Q (paths i) ≠ 0 := by
  have hB := exists_nonzero_monomials_iff_path
    ((LinearMap.fst ℂ ℂ ℂ).comp Q) paths degrees hd s hs
  have hW := exists_nonzero_monomials_iff_path
    ((LinearMap.snd ℂ ℂ ℂ).comp Q) paths degrees hd s hs
  simpa only [LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or,
    and_or_left, exists_or] using hB.or hW

end
end Math.PolynomialSelectedPaths
