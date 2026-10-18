import Physics.FieldTheory.Spinor.WeylSpinor
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Uniqueness of the two-left/two-right Weyl-spinor contraction. -/
namespace GUT.WeylSpinorUniqueness
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor WeylSpinor
open scoped TensorProduct Matrix

abbrev Coefficient := IntertwiningMap ((left.tprod left).tprod (right.tprod right))
  (Representation.trivial ℂ WeylSpinor.Group ℂ)

def basisValue (f : Coefficient) (i j k l : Fin 2) : ℂ :=
  f ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))

private theorem basisValue_eq (f : Coefficient) (i j k l : Fin 2) :
    basisValue f i j k l =
      f ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) := rfl

private def diagonal : WeylSpinor.Group :=
  ⟨!![1 + Complex.I, 0; 0, (1 - Complex.I) / 2], by
    norm_num [Matrix.det_fin_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im]⟩

private def shear : WeylSpinor.Group :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

private def eigenvalue (i : Fin 2) : ℂ := ![1 + Complex.I, (1 - Complex.I) / 2] i

private theorem diagonal_left (i : Fin 2) :
    left diagonal (weakBasis i) = eigenvalue i • weakBasis i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [left, diagonal, eigenvalue, weakBasis, Matrix.mulVec]

private theorem diagonal_right (i : Fin 2) :
    right diagonal (weakBasis i) = star (eigenvalue i) • weakBasis i := by
  rw [right_apply]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonal, eigenvalue, weakBasis, Matrix.mulVec, map_ofNat]

private theorem diagonal_constraint (f : Coefficient) (i j k l : Fin 2) :
    (eigenvalue i * eigenvalue j * star (eigenvalue k) * star (eigenvalue l) - 1) *
      basisValue f i j k l = 0 := by
  have h := IntertwiningMap.isIntertwining _ _ f diagonal
    ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))
  simp only [Representation.tprod_apply, TensorProduct.map_tmul, diagonal_left,
    diagonal_right, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul] at h
  change star (eigenvalue l) • star (eigenvalue k) • eigenvalue j • eigenvalue i •
    basisValue f i j k l = basisValue f i j k l at h
  simp only [smul_eq_mul] at h
  linear_combination h

theorem basisValue_vanish (f : Coefficient) (i j k l : Fin 2)
    (h : i = j ∨ k = l) : basisValue f i j k l = 0 := by
  have hc := diagonal_constraint f i j k l
  have hn : eigenvalue i * eigenvalue j * star (eigenvalue k) * star (eigenvalue l) - 1 ≠ 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals norm_num at h
    all_goals norm_num [eigenvalue, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  exact (mul_eq_zero.mp hc).resolve_left hn

private theorem shear_left_zero : left shear (weakBasis 0) = weakBasis 0 := by
  ext i
  fin_cases i <;> simp [left, shear, weakBasis, Matrix.mulVec]

private theorem shear_left_one : left shear (weakBasis 1) = weakBasis 0 + weakBasis 1 := by
  ext i
  fin_cases i <;> simp [left, shear, weakBasis, Matrix.mulVec]

private theorem shear_right_zero : right shear (weakBasis 0) = weakBasis 0 := by
  rw [right_apply]
  ext i
  fin_cases i <;> simp [shear, weakBasis, Matrix.mulVec]

private theorem shear_right_one : right shear (weakBasis 1) = weakBasis 0 + weakBasis 1 := by
  rw [right_apply]
  ext i
  fin_cases i <;> simp [shear, weakBasis, Matrix.mulVec]

private theorem shear_constraint (f : Coefficient) (i j k l : Fin 2) :
    f (((left shear (weakBasis i)) ⊗ₜ[ℂ] (left shear (weakBasis j))) ⊗ₜ[ℂ]
      ((right shear (weakBasis k)) ⊗ₜ[ℂ] (right shear (weakBasis l)))) =
        basisValue f i j k l :=
  IntertwiningMap.isIntertwining _ _ f shear
    ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))

theorem basisValue_swap_left (f : Coefficient) (k l : Fin 2) :
    basisValue f 1 0 k l = -basisValue f 0 1 k l := by
  have h := shear_constraint f 1 1 k l
  fin_cases k <;> fin_cases l
  all_goals simp only [Fin.mk_zero, Fin.mk_one] at h ⊢
  all_goals simp only [shear_left_one, shear_right_zero, shear_right_one,
      TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ← basisValue_eq] at h
  all_goals simp only [basisValue_vanish f 0 0 _ _ (Or.inl rfl),
    basisValue_vanish f 1 1 _ _ (Or.inl rfl),
    basisValue_vanish f _ _ 0 0 (Or.inr rfl),
    basisValue_vanish f _ _ 1 1 (Or.inr rfl)] at h ⊢
  all_goals try norm_num
  all_goals linear_combination h

theorem basisValue_swap_right (f : Coefficient) :
    basisValue f 0 1 1 0 = -basisValue f 0 1 0 1 := by
  have h := shear_constraint f 0 1 1 1
  simp only [shear_left_zero, shear_left_one, shear_right_one,
    TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, ← basisValue_eq] at h
  simp only [basisValue_vanish f 0 0 _ _ (Or.inl rfl),
    basisValue_vanish f _ _ 0 0 (Or.inr rfl),
    basisValue_vanish f _ _ 1 1 (Or.inr rfl)] at h
  linear_combination h

theorem basisValue_formula (f : Coefficient) (i j k l : Fin 2) :
    basisValue f i j k l = basisValue f 0 1 0 1 *
      (eps2 (weakBasis i) (weakBasis j) * eps2 (weakBasis k) (weakBasis l)) := by
  by_cases h : i = j ∨ k = l
  · rw [basisValue_vanish f i j k l h]
    rcases h with h | h
    · subst j; simp [eps2, mul_comm]
    · subst l; simp [eps2, mul_comm]
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals norm_num at h
    all_goals simp only [Fin.mk_zero, Fin.mk_one]
    all_goals try simp only [basisValue_swap_left f, basisValue_swap_right f]
    all_goals norm_num [eps2, weakBasis, Pi.single_apply]

theorem eq_smul_four (f : Coefficient) : f = basisValue f 0 1 0 1 • four := by
  apply IntertwiningMap.ext
  let b := Pi.basisFun ℂ (Fin 2)
  apply ((b.tensorProduct b).tensorProduct (b.tensorProduct b)).ext
  rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
  simp only [Module.Basis.tensorProduct_apply, b, Pi.basisFun_apply]
  change basisValue f i j k l = basisValue f 0 1 0 1 *
    (eps2 (weakBasis i) (weakBasis j) * eps2 (weakBasis k) (weakBasis l))
  exact basisValue_formula f i j k l

end
end GUT.WeylSpinorUniqueness
