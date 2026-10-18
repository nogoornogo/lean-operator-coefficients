import Math.RepresentationTheory.Multiplicity.HilbertMultiplicityOperator
import Mathlib.LinearAlgebra.Determinant

/-!
# The weighted determinant is the actual operator determinant

Ordinary constituent bases suffice for determinants. Adjoint compatibility
is established separately using the inherited Hilbert inner products in
`HilbertMultiplicityOperator`; no arbitrary basis is assumed orthonormal.
-/

namespace Math.HilbertMultiplicityOperator

noncomputable section

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem amplify_mulVec (m n : I → ℕ) (A : Matrices m)
    (x : MultiplicityMatrix.Coordinates m n → ℂ) (i : I) (a : Fin (m i)) (k : Fin (n i)) :
    (MultiplicityMatrix.amplify m n A *ᵥ x) ⟨i, a, k⟩ =
      ∑ b, A i a b * x ⟨i, b, k⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp [MultiplicityMatrix.amplify, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro b _
    rw [MultiplicityMatrix.amplify, Matrix.blockDiagonal'_apply_ne _ _ _ hji.symm, zero_mul]
  · simp

variable (m : I → ℕ) (S : I → Type*)
  [∀ i, NormedAddCommGroup (S i)] [∀ i, InnerProductSpace ℂ (S i)]
  [∀ i, FiniteDimensional ℂ (S i)]

/-- Actual constituent dimensions, not free exponent parameters. -/
abbrev dimensions (i : I) := Module.finrank ℂ (S i)

/-- Linear coordinates displaying a block as multiplicity index times constituent index. -/
def coordinates : Space m S ≃ₗ[ℂ] (MultiplicityMatrix.Coordinates m (dimensions S) → ℂ) where
  toFun x a := (Module.finBasis ℂ (S a.1)).equivFun (x a.1 a.2.1) a.2.2
  invFun y := WithLp.toLp 2 fun i => WithLp.toLp 2 fun a =>
    (Module.finBasis ℂ (S i)).equivFun.symm (fun k => y ⟨i, a, k⟩)
  left_inv x := by
    ext i a
    exact (Module.finBasis ℂ (S i)).equivFun.symm_apply_apply (x i a)
  right_inv y := by
    funext a
    exact congrFun ((Module.finBasis ℂ (S a.1)).equivFun.apply_symm_apply
      (fun k => y ⟨a.1, a.2.1, k⟩)) a.2.2
  map_add' x y := by ext a; simp
  map_smul' z x := by ext a; simp

theorem coordinates_operator (A : Matrices m) (x : Space m S) :
    coordinates m S (operator m S A x) =
      MultiplicityMatrix.amplify m (dimensions S) A *ᵥ coordinates m S x := by
  funext ⟨i, a, k⟩
  rw [amplify_mulVec]
  change (Module.finBasis ℂ (S i)).equivFun (∑ b, A i a b • x i b) k = _
  simp [map_sum, coordinates]

theorem coordinates_conj_operator (A : Matrices m) :
    (coordinates m S).conj (operator m S A).toLinearMap =
      Matrix.toLin' (MultiplicityMatrix.amplify m (dimensions S) A) := by
  apply LinearMap.ext
  intro x
  simpa using coordinates_operator m S A ((coordinates m S).symm x)

/-- Determinants on the actual Hilbert sum have the constituent-dimension exponents. -/
theorem det_operator (A : Matrices m) :
    LinearMap.det (operator m S A).toLinearMap = ∏ i, (A i).det ^ Module.finrank ℂ (S i) := by
  classical
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  rw [← LinearMap.det_conj (operator m S A).toLinearMap (coordinates m S)]
  change LinearMap.det ((coordinates m S).conj (operator m S A).toLinearMap) = _
  rw [coordinates_conj_operator, LinearMap.det_toLin', MultiplicityMatrix.det_amplify]

end

end Math.HilbertMultiplicityOperator
