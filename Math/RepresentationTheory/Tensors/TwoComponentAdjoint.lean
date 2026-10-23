import Math.RepresentationTheory.Symmetric.TwoComponentSymmetricTensor
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The concrete triplet is the traceless two-by-two conjugation module. -/
namespace Math.TwoComponentAdjoint
set_option autoImplicit false
noncomputable section
open TwoComponentSymmetricTensor Matrix

abbrev Traceless := LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℂ ℂ :
  Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ)

def matrix : Triplet →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun z := !![-z 1,z 0;-z 2,z 1]
  map_add' z w := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c z := by ext i j; fin_cases i <;> fin_cases j <;> simp

def intoTraceless : Triplet →ₗ[ℂ] Traceless := matrix.codRestrict _ (by
  intro z
  simp [LinearMap.mem_ker, matrix, Matrix.trace, Fin.sum_univ_two])

def fromTraceless : Traceless →ₗ[ℂ] Triplet where
  toFun m := ![m.val 0 1,-m.val 0 0,-m.val 1 0]
  map_add' m n := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c m := by ext i; fin_cases i <;> simp

def equiv : Triplet ≃ₗ[ℂ] Traceless where
  toLinearMap := intoTraceless
  invFun := fromTraceless
  left_inv z := by ext i; fin_cases i <;> simp [fromTraceless, intoTraceless, matrix]
  right_inv m := by
    have hm : m.val 0 0 + m.val 1 1 = 0 := by
      have h := m.property
      change Matrix.trace m.val = 0 at h
      simpa only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] using h
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fromTraceless, intoTraceless, matrix]
    linear_combination -hm

theorem matrix_transform (m : Matrix (Fin 2) (Fin 2) ℂ) (z : Triplet) :
    matrix ((squareMatrix m).mulVec z) * m = m.det • (m * matrix z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, squareMatrix, Matrix.mul_apply, Matrix.det_fin_two,
      Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem conjugation (g : TwoComponentSymmetricTensor.Group) (z : Triplet) :
    matrix (triplet g z) = (g : Matrix (Fin 2) (Fin 2) ℂ) * matrix z *
      (g⁻¹ : TwoComponentSymmetricTensor.Group) := by
  have h := matrix_transform (g : Matrix (Fin 2) (Fin 2) ℂ) z
  rw [g.property, one_smul] at h
  have hg : (g : Matrix (Fin 2) (Fin 2) ℂ) *
      (g⁻¹ : TwoComponentSymmetricTensor.Group) = 1 := by
    change ((g*g⁻¹ : TwoComponentSymmetricTensor.Group) : Matrix (Fin 2) (Fin 2) ℂ) = 1
    simp
  change matrix ((squareMatrix (g : Matrix (Fin 2) (Fin 2) ℂ)).mulVec z) = _
  calc
    _ = matrix ((squareMatrix (g : Matrix (Fin 2) (Fin 2) ℂ)).mulVec z) *
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * (g⁻¹ : TwoComponentSymmetricTensor.Group)) := by rw [hg]; simp
    _ = _ := by rw [← Matrix.mul_assoc, h]

end
end Math.TwoComponentAdjoint
