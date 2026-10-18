import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Degree-uniform exterior characters from a diagonal basis. The finite
product is a symbolic identity, not a table of evaluated degrees. -/
namespace Math.ExteriorCharacterPolynomial
set_option autoImplicit false
open scoped BigOperators
open Polynomial

variable {I R : Type*} [Fintype I] [CommRing R]

noncomputable def generating (a : I → R) : R[X] :=
  ∏ i, (1 + C (a i) * X)

omit [Fintype I] in
/-- The symbolic include/exclude recurrence for adjoining one basis slot. -/
theorem coeff_insert [DecidableEq I] (a : I → R) (s : Finset I) (i : I)
    (hi : i ∉ s) (n : ℕ) :
    (∏ j ∈ insert i s, (1 + C (a j) * X : R[X])).coeff (n+1) =
      (∏ j ∈ s, (1 + C (a j) * X : R[X])).coeff (n+1) +
        a i * (∏ j ∈ s, (1 + C (a j) * X : R[X])).coeff n := by
  rw [Finset.prod_insert hi, add_mul, one_mul, coeff_add]
  congr 1
  rw [mul_assoc, coeff_C_mul, coeff_X_mul]

theorem generating_coeff (a : I → R) (n : ℕ) :
    (generating a).coeff n =
      ∑ s : Set.powersetCard I n, ∏ i ∈ (s : Finset I), a i := by
  classical
  have hp (s : Finset I) :
      (∏ i ∈ s, (C (a i) * X : R[X])) =
        monomial s.card (∏ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, ih, Finset.card_insert_of_notMem hi,
        Finset.prod_insert hi]
      simp [mul_assoc, X_mul_monomial, C_mul_monomial]
  unfold generating
  rw [Finset.prod_one_add]
  simp_rw [hp, finsetSum_coeff, coeff_monomial]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun s hs => (⟨s, Set.powersetCard.mem_iff.mpr (Finset.mem_filter.mp hs).2⟩ : Set.powersetCard I n))
  · intro s hs; simp
  · intro s hs t ht h; exact congrArg Subtype.val h
  · intro s hs
    refine ⟨s.val, ?_, ?_⟩
    · simp
    · rfl
  · intro s hs; rfl

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]


theorem exterior_character (rho : Representation ℂ G V)
    (b : Module.Basis I ℂ V) (g : G) (a : I → ℂ)
    (ha : ∀ i, rho g (b i) = a i • b i) (n : ℕ) :
    (rho.exteriorPower n).character g = (generating a).coeff n := by
  rw [generating_coeff]
  exact exteriorPower.trace_map_of_apply_basis b (rho g) a n ha

end Math.ExteriorCharacterPolynomial
