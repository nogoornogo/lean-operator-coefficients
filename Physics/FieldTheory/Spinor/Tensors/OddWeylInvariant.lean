import Physics.FieldTheory.Spinor.Weyl.FourSameWeylCompleteness
import Mathlib.LinearAlgebra.TensorProduct.Basis

open Math

/-! No scalar invariant has three Weyl slots of one chirality and one of the
other. The proof uses a nonunitary SL(2,C) diagonal element; restriction to
SU(2) alone would not prove this statement. -/
namespace Physics.OddWeylInvariant
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor WeylSpinor
open scoped TensorProduct Matrix

def representation (rightHanded : Bool) :=
  ((FourSameWeylCompleteness.action rightHanded).tprod
    (FourSameWeylCompleteness.action rightHanded)).tprod
      ((FourSameWeylCompleteness.action rightHanded).tprod
        (FourSameWeylCompleteness.action (!rightHanded)))
abbrev Coefficient (rightHanded : Bool) := IntertwiningMap (representation rightHanded)
  (Representation.trivial ℂ WeylSpinor.Group ℂ)

private def diagonal : WeylSpinor.Group :=
  ⟨!![1 + Complex.I, 0; 0, (1 - Complex.I) / 2], by
    norm_num [Matrix.det_fin_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im]⟩

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

private theorem multiplier_ne_one (i j k l : Fin 2) :
    eigenvalue i * eigenvalue j * eigenvalue k * star (eigenvalue l) - 1 ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [eigenvalue, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- The same separating element works in every typed slot order. -/
def testElement : WeylSpinor.Group := diagonal
def slotEigen (rightHanded : Bool) (i : Fin 2) : ℂ :=
  if rightHanded then star (eigenvalue i) else eigenvalue i

theorem test_basis (rightHanded : Bool) (i : Fin 2) :
    FourSameWeylCompleteness.action rightHanded testElement (weakBasis i) =
      slotEigen rightHanded i • weakBasis i := by
  cases rightHanded
  · exact diagonal_left i
  · exact diagonal_right i

theorem odd_product_ne_one (b0 b1 b2 b3 : Bool)
    (h : ((if b0 then 0 else 1) + (if b1 then 0 else 1) +
      (if b2 then 0 else 1) + (if b3 then 0 else 1) : ℕ) % 2 = 1)
    (i j k l : Fin 2) :
    slotEigen b0 i * slotEigen b1 j * slotEigen b2 k * slotEigen b3 l - 1 ≠ 0 := by
  have hs (i j k l : Fin 2) :
      star (eigenvalue i) * star (eigenvalue j) * star (eigenvalue k) * eigenvalue l - 1 ≠ 0 := by
    have he := star_ne_zero.mpr (multiplier_ne_one i j k l)
    simp only [star_sub, star_mul, star_star, star_one] at he
    convert he using 1; ring
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp only [Bool.false_eq_true,
    ↓reduceIte] at h ⊢
  all_goals norm_num at h
  all_goals dsimp [slotEigen]
  · exact multiplier_ne_one i j k l
  · convert multiplier_ne_one i j l k using 1; simp only [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]
  · convert multiplier_ne_one i k l j using 1; simp only [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]
  · convert hs j k l i using 1; simp only [starRingEnd_apply, mul_comm, mul_assoc]
  · convert multiplier_ne_one j k l i using 1; simp only [starRingEnd_apply, mul_comm, mul_assoc]
  · convert hs i k l j using 1; simp only [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]
  · convert hs i j l k using 1; simp only [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]
  · exact hs i j k l

theorem left_three_eq_zero (f : Coefficient false) : f = 0 := by
  have hb (i j k l : Fin 2) :
      f ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) = 0 := by
    have h := IntertwiningMap.isIntertwining _ _ f diagonal
      ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))
    simp only [representation, FourSameWeylCompleteness.action, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, Representation.tprod_apply, TensorProduct.map_tmul,
      diagonal_left, diagonal_right, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, smul_smul,
      Representation.trivial_apply] at h
    change f.toLinearMap ((star (eigenvalue l) * eigenvalue k * (eigenvalue j * eigenvalue i)) •
      ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))) =
      f.toLinearMap ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) at h
    rw [map_smul, smul_eq_mul] at h
    have hc : (eigenvalue i * eigenvalue j * eigenvalue k * star (eigenvalue l) - 1) *
        f ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hc).resolve_left (multiplier_ne_one i j k l)
  apply IntertwiningMap.ext
  ext i j k l
  exact hb i j k l

theorem right_three_eq_zero (f : Coefficient true) : f = 0 := by
  have hb (i j k l : Fin 2) :
      f ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) = 0 := by
    have h := IntertwiningMap.isIntertwining _ _ f diagonal
      ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))
    change f ((right diagonal (weakBasis i) ⊗ₜ[ℂ] right diagonal (weakBasis j)) ⊗ₜ[ℂ]
      (right diagonal (weakBasis k) ⊗ₜ[ℂ] left diagonal (weakBasis l))) = f _ at h
    rw [diagonal_right, diagonal_right, diagonal_right, diagonal_left] at h
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul] at h
    change f.toLinearMap ((eigenvalue l * star (eigenvalue k) *
      (star (eigenvalue j) * star (eigenvalue i))) •
      ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l))) =
      f.toLinearMap ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) at h
    rw [map_smul, smul_eq_mul] at h
    have hn : star (eigenvalue i) * star (eigenvalue j) * star (eigenvalue k) * eigenvalue l - 1 ≠ 0 := by
      have hs := star_ne_zero.mpr (multiplier_ne_one i j k l)
      simp only [star_sub, star_mul, star_star, star_one] at hs
      convert hs using 1; ring
    apply (mul_eq_zero.mp (show (star (eigenvalue i) * star (eigenvalue j) *
      star (eigenvalue k) * eigenvalue l - 1) *
      f ((weakBasis i ⊗ₜ[ℂ] weakBasis j) ⊗ₜ[ℂ] (weakBasis k ⊗ₜ[ℂ] weakBasis l)) = 0 from ?_)).resolve_left hn
    linear_combination h
  apply IntertwiningMap.ext
  ext i j k l
  exact hb i j k l

theorem eq_zero (rightHanded : Bool) (f : Coefficient rightHanded) : f = 0 := by
  cases rightHanded
  · exact left_three_eq_zero f
  · exact right_three_eq_zero f

/-- Arbitrary independent gauge/flavor spectators cannot restore an invariant. -/
theorem external_eq_zero {R V : Type*} [Group R] [AddCommMonoid V] [Module ℂ V]
    (rightHanded : Bool) (v : Representation ℂ R V)
    (f : IntertwiningMap (ExternalInvariantTensor.external (representation rightHanded) v)
      (Representation.trivial ℂ (WeylSpinor.Group × R) ℂ)) : f = 0 := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  exact DFunLike.congr_fun (eq_zero rightHanded
    (ExternalInvariantFactorization.leftSlice (representation rightHanded) v f y)) x

end
end Physics.OddWeylInvariant
