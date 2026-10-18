import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Concrete symmetric two-component tensors, with the middle coordinate
equal to half the sum of the two mixed components. -/
namespace Math.TwoComponentSymmetricTensor
set_option autoImplicit false
noncomputable section
open Representation Matrix
open scoped TensorProduct

abbrev Group := Matrix.SpecialLinearGroup (Fin 2) ℂ
abbrev Doublet := Fin 2 → ℂ
abbrev Triplet := Fin 3 → ℂ

@[simp] theorem vector_third (x y z : ℂ) : (![x,y,z] : Triplet) 2 = z := rfl

def doublet : Representation ℂ Group Doublet where
  toFun g := Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

def squareMatrix (m : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![m 0 0 ^ 2, 2 * m 0 0 * m 0 1, m 0 1 ^ 2;
     m 0 0 * m 1 0, m 0 0 * m 1 1 + m 0 1 * m 1 0, m 0 1 * m 1 1;
     m 1 0 ^ 2, 2 * m 1 0 * m 1 1, m 1 1 ^ 2]

theorem squareMatrix_one : squareMatrix (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [squareMatrix]

theorem squareMatrix_mul (m n : Matrix (Fin 2) (Fin 2) ℂ) :
    squareMatrix (m * n) = squareMatrix m * squareMatrix n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squareMatrix, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

def triplet : Representation ℂ Group Triplet where
  toFun g := Matrix.toLin' (squareMatrix (g : Matrix (Fin 2) (Fin 2) ℂ))
  map_one' := by rw [show ((1 : Group) : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl,
    squareMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [show ((g * h : Group) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
      squareMatrix_mul, Matrix.toLin'_mul]; rfl

def pairBilin : Doublet →ₗ[ℂ] Doublet →ₗ[ℂ] Triplet :=
  LinearMap.mk₂ ℂ (fun x y => ![x 0 * y 0,
    (x 0 * y 1 + x 1 * y 0) / 2, x 1 * y 1])
    (by intro x x' y; ext i; fin_cases i <;> simp <;> ring)
    (by intro z x y; ext i; fin_cases i <;> simp <;> ring)
    (by intro x y y'; ext i; fin_cases i <;> simp <;> ring)
    (by intro z x y; ext i; fin_cases i <;> simp <;> ring)

def pair : IntertwiningMap (doublet.tprod doublet) triplet where
  toLinearMap := TensorProduct.lift pairBilin
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    ext i
    fin_cases i <;>
      simp [pairBilin, doublet, triplet, squareMatrix, Matrix.mulVec,
        ] <;> ring

@[simp] theorem pair_tmul (x y : Doublet) :
    pair (x ⊗ₜ[ℂ] y) = ![x 0 * y 0,
      (x 0 * y 1 + x 1 * y 0) / 2, x 1 * y 1] := rfl

theorem pair_symmetric (x y : Doublet) : pair (x ⊗ₜ[ℂ] y) = pair (y ⊗ₜ[ℂ] x) := by
  ext i
  fin_cases i <;> simp <;> ring

end
end Math.TwoComponentSymmetricTensor
