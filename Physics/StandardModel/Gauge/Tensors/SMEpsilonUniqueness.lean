import Physics.StandardModel.Gauge.Tensors.SMEpsilonTensor
import Math.RepresentationTheory.Unitary.SmallSpecialUnitary

open Math

/-! Uniqueness of the standard weak and color invariant contractions. -/
namespace Physics.SMEpsilonUniqueness
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor SmallSpecialUnitary

private theorem fin_three_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

private theorem phase_basis (i : Fin 2) :
    defining 2 phaseTwo (weakBasis i) =
      (if i = 0 then Complex.I else -Complex.I) • weakBasis i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [defining, phaseTwo, weakBasis, Matrix.mulVec]

private theorem flip_zero : defining 2 flipTwo (weakBasis 0) = -weakBasis 1 := by
  ext i
  fin_cases i <;> simp [defining, flipTwo, weakBasis, Matrix.mulVec]

private theorem flip_one : defining 2 flipTwo (weakBasis 1) = weakBasis 0 := by
  ext i
  fin_cases i <;> simp [defining, flipTwo, weakBasis, Matrix.mulVec]

theorem weak_unique (f : Weak →ₗ[ℂ] Weak →ₗ[ℂ] ℂ)
    (hf : ∀ g x y, f (defining 2 g x) (defining 2 g y) = f x y) :
    f = f (weakBasis 0) (weakBasis 1) • eps2Bilin := by
  have hz (i : Fin 2) : f (weakBasis i) (weakBasis i) = 0 := by
    have h := hf phaseTwo (weakBasis i) (weakBasis i)
    simp only [phase_basis, map_smul, LinearMap.smul_apply] at h
    fin_cases i
    all_goals simp only [Fin.mk_zero, Fin.mk_one] at h ⊢
    all_goals simp [smul_eq_mul, ← mul_assoc] at h
    all_goals linear_combination -(1 / 2 : ℂ) * h
  have hs : f (weakBasis 1) (weakBasis 0) = -f (weakBasis 0) (weakBasis 1) := by
    have h := hf flipTwo (weakBasis 0) (weakBasis 1)
    rw [flip_zero, flip_one, map_neg, LinearMap.neg_apply] at h
    linear_combination -h
  apply (Pi.basisFun ℂ (Fin 2)).ext
  intro i
  apply (Pi.basisFun ℂ (Fin 2)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change f (weakBasis i) (weakBasis j) =
    f (weakBasis 0) (weakBasis 1) * eps2 (weakBasis i) (weakBasis j)
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.mk_zero, Fin.mk_one]
  all_goals try simp only [hz, hs]
  all_goals norm_num [eps2, weakBasis]

private theorem sign_basis (n i : Fin 3) :
    defining 3 (diagonalSign n) (colorBasis i) = signAt n i • colorBasis i := by
  ext j
  by_cases h : j = i
  · subst j; simp [defining, diagonalSign, Matrix.mulVec_diagonal, colorBasis]
  · simp [defining, diagonalSign, Matrix.mulVec_diagonal, colorBasis, h]

private theorem swap_basis (m n i : Fin 3) (hmn : m ≠ n) :
    defining 3 (signedPermutation (Equiv.swap m n)) (colorBasis i) =
      -colorBasis (Equiv.swap m n i) := by
  ext j
  simp [defining, signedPermutation, Equiv.Perm.sign_swap hmn, colorBasis,
    Matrix.toLin'_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem color_basis_vanish (f : Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ)
    (hf : ∀ g x y z, f (defining 3 g x) (defining 3 g y) (defining 3 g z) = f x y z)
    (i j k : Fin 3) (h : ¬(i ≠ j ∧ i ≠ k ∧ j ≠ k)) :
    f (colorBasis i) (colorBasis j) (colorBasis k) = 0 := by
  have hc (n : Fin 3) := hf (diagonalSign n) (colorBasis i) (colorBasis j) (colorBasis k)
  simp only [sign_basis, map_smul, LinearMap.smul_apply, smul_eq_mul] at hc
  have h0 := hc 0
  have h1 := hc 1
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at h
  all_goals simp only [Fin.mk_zero, Fin.mk_one] at h0 h1 ⊢
  all_goals norm_num [signAt] at h0 h1 ⊢
  all_goals first | linear_combination -(1 / 2 : ℂ) * h0 | linear_combination -(1 / 2 : ℂ) * h1

theorem color_unique (f : Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ)
    (hf : ∀ g x y z, f (defining 3 g x) (defining 3 g y) (defining 3 g z) = f x y z) :
    f = f (colorBasis 0) (colorBasis 1) (colorBasis 2) • eps3Trilin := by
  have hs (m n i j k : Fin 3) (hmn : m ≠ n) :
      f (colorBasis (Equiv.swap m n i)) (colorBasis (Equiv.swap m n j))
        (colorBasis (Equiv.swap m n k)) = -f (colorBasis i) (colorBasis j) (colorBasis k) := by
    have h := hf (signedPermutation (Equiv.swap m n)) (colorBasis i) (colorBasis j) (colorBasis k)
    simp only [swap_basis _ _ _ hmn, map_neg, LinearMap.neg_apply] at h
    linear_combination -h
  have h102 := hs 0 1 0 1 2 (by decide)
  have h021 := hs 1 2 0 1 2 (by decide)
  have h210 := hs 0 2 0 1 2 (by decide)
  have h120 := hs 0 1 0 2 1 (by decide)
  have h201 := hs 1 2 1 0 2 (by decide)
  norm_num [Equiv.swap_apply_def, Fin.ext_iff] at h102 h021 h210 h120 h201
  apply (Pi.basisFun ℂ (Fin 3)).ext
  intro i
  apply (Pi.basisFun ℂ (Fin 3)).ext
  intro j
  apply (Pi.basisFun ℂ (Fin 3)).ext
  intro k
  simp only [Pi.basisFun_apply]
  change f (colorBasis i) (colorBasis j) (colorBasis k) =
    f (colorBasis 0) (colorBasis 1) (colorBasis 2) * eps3 (colorBasis i) (colorBasis j) (colorBasis k)
  by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
  · fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at h
    all_goals simp only [Fin.mk_zero, Fin.mk_one, fin_three_two]
    all_goals norm_num [eps3, colorBasis, Pi.single_apply, Fin.ext_iff] at h102 h021 h210 h120 h201 ⊢
    all_goals first | linear_combination h102 | linear_combination h021 |
      linear_combination h210 | linear_combination h120 - h021 | linear_combination h201 - h102
  · rw [color_basis_vanish f hf i j k h]
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at h
    all_goals norm_num [eps3, colorBasis, Pi.single_apply, Fin.ext_iff]

end
end Physics.SMEpsilonUniqueness
