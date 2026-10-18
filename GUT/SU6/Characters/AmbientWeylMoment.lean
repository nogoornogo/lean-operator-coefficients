import GUT.SU6.Characters.DegreeFiveWeylInvariant
import Mathlib.Tactic

/-!
# Ambient Weyl-invariant weight moments

This file gives a canonical finite `Finsupp` model for the part of an
`SU(6)` virtual character needed by the hypercharge argument.  A weight is
represented by its unique rational six-vector with coordinate sum zero, and
a finite virtual weight character is an integer-valued `Finsupp` on these
weights.

The full symmetric group permutes the six weight coordinates.  Lean proves
that the fifth weight-moment polynomial of a Weyl-invariant character is
symmetric and homogeneous of degree five.  Combining this with
`DegreeFiveWeylInvariant` puts its trace-zero restriction in the span of
`p5` and `p2*p3`.
-/

open scoped BigOperators

namespace GUT
namespace AmbientWeylMoment

open MvPolynomial

noncomputable section

/-- A canonical rational representative of an `SU(6)` torus weight. -/
structure Weight where
  coord : Fin 6 → ℚ
  sum_zero : ∑ i, coord i = 0

@[ext]
theorem Weight.ext {w v : Weight} (h : w.coord = v.coord) : w = v := by
  cases w
  cases v
  simp_all

/-- Permute weight coordinates compatibly with `MvPolynomial.rename`. -/
def permuteWeight (e : Equiv.Perm (Fin 6)) (w : Weight) : Weight where
  coord := w.coord ∘ e.symm
  sum_zero := by
    change ∑ i, w.coord (e.symm i) = 0
    rw [Equiv.sum_comp e.symm w.coord]
    exact w.sum_zero

@[simp]
theorem permuteWeight_coord (e : Equiv.Perm (Fin 6)) (w : Weight) (i : Fin 6) :
    (permuteWeight e w).coord i = w.coord (e.symm i) := rfl

def permuteWeightEquiv (e : Equiv.Perm (Fin 6)) : Weight ≃ Weight where
  toFun := permuteWeight e
  invFun := permuteWeight e.symm
  left_inv w := by
    ext i
    simp [permuteWeight]
  right_inv w := by
    ext i
    simp [permuteWeight]

theorem permuteWeight_injective (e : Equiv.Perm (Fin 6)) :
    Function.Injective (permuteWeight e) :=
  (permuteWeightEquiv e).injective

/-- A normalized finite virtual ambient weight character. -/
abbrev Character := Weight →₀ ℤ

def permuteCharacter (e : Equiv.Perm (Fin 6)) (χ : Character) : Character :=
  Finsupp.mapDomain (permuteWeight e) χ

def IsWeylInvariant (χ : Character) : Prop :=
  ∀ e : Equiv.Perm (Fin 6), permuteCharacter e χ = χ

/-- The linear weight functional as a polynomial in six Cartan coordinates. -/
def linearPolynomial (w : Weight) : MvPolynomial (Fin 6) ℚ :=
  ∑ i, C (w.coord i) * X i

theorem linearPolynomial_isHomogeneous (w : Weight) :
    (linearPolynomial w).IsHomogeneous 1 := by
  rw [linearPolynomial]
  apply IsHomogeneous.sum
  intro i _hi
  exact (isHomogeneous_X ℚ i).C_mul _

theorem rename_linearPolynomial (e : Equiv.Perm (Fin 6)) (w : Weight) :
    rename e (linearPolynomial w) = linearPolynomial (permuteWeight e w) := by
  change rename e (∑ i, C (w.coord i) * X i) =
    ∑ i, C (w.coord (e.symm i)) * X i
  rw [map_sum]
  simp_rw [map_mul, rename_C, rename_X]
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  simp

/-- The degree-five Taylor moment attached to a finite virtual weight
character. -/
def fifthMomentPolynomial (χ : Character) : MvPolynomial (Fin 6) ℚ :=
  χ.sum fun w c => C (c : ℚ) * (linearPolynomial w) ^ 5

theorem fifthMomentPolynomial_isHomogeneous (χ : Character) :
    (fifthMomentPolynomial χ).IsHomogeneous 5 := by
  rw [fifthMomentPolynomial, Finsupp.sum]
  apply IsHomogeneous.sum
  intro w _hw
  simpa using (linearPolynomial_isHomogeneous w).pow 5 |>.C_mul (χ w : ℚ)

theorem rename_fifthMomentPolynomial
    (e : Equiv.Perm (Fin 6)) (χ : Character) :
    rename e (fifthMomentPolynomial χ) =
      fifthMomentPolynomial (permuteCharacter e χ) := by
  unfold fifthMomentPolynomial permuteCharacter
  rw [Finsupp.sum_mapDomain_index_inj (permuteWeight_injective e)]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro w _hw
  simp [rename_linearPolynomial]

theorem fifthMomentPolynomial_isSymmetric
    (χ : Character) (hχ : IsWeylInvariant χ) :
    (fifthMomentPolynomial χ).IsSymmetric := by
  intro e
  rw [rename_fifthMomentPolynomial, hχ e]

/-- Direct finite-sum form of the fifth weight moment. -/
def fifthMomentValue (χ : Character) (x : Fin 6 → ℚ) : ℚ :=
  χ.sum fun w c => (c : ℚ) * (∑ i, w.coord i * x i) ^ 5

theorem eval_linearPolynomial (w : Weight) (x : Fin 6 → ℚ) :
    eval x (linearPolynomial w) = ∑ i, w.coord i * x i := by
  simp [linearPolynomial]

theorem eval_fifthMomentPolynomial (χ : Character) (x : Fin 6 → ℚ) :
    eval x (fifthMomentPolynomial χ) = fifthMomentValue χ x := by
  rw [fifthMomentPolynomial, fifthMomentValue, map_finsuppSum]
  apply Finsupp.sum_congr
  intro w _hw
  simp [eval_linearPolynomial]

theorem fifthMoment_traceZero_span
    (χ : Character) (hχ : IsWeylInvariant χ) :
    ∃ A B : ℚ, ∀ x : Fin 6 → ℚ, (∑ i, x i) = 0 →
      fifthMomentValue χ x =
        A * DegreeFiveWeylInvariant.powerSumValue x 5 +
          B * (DegreeFiveWeylInvariant.powerSumValue x 2 *
            DegreeFiveWeylInvariant.powerSumValue x 3) := by
  rcases DegreeFiveWeylInvariant.symmetric_degreeFive_traceZero_span
      (fifthMomentPolynomial χ)
      (fifthMomentPolynomial_isSymmetric χ hχ)
      (fifthMomentPolynomial_isHomogeneous χ) with ⟨A, B, hAB⟩
  exact ⟨A, B, fun x hx => by
    rw [← eval_fifthMomentPolynomial]
    exact hAB x hx⟩

end
end AmbientWeylMoment
end GUT
