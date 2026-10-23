import Math.Algebra.Constructions.FormalConnection
import Math.Algebra.Jets.ScalarJetAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-! Entrywise ordinary jet derivatives produce actual noncommuting matrix
connections; matrix multiplication is internal, not field statistics. -/
namespace Math.FormalConnection
set_option autoImplicit false
noncomputable section

variable {S I N : Type*} [Fintype N] [DecidableEq N]

def matrixDerivative (i : I) :
    Matrix N N (ScalarJetAlgebra.Algebra S I) →ₗ[ℂ] Matrix N N (ScalarJetAlgebra.Algebra S I) :=
  (ScalarJetAlgebra.totalDerivative i).toLinearMap.mapMatrix

omit [Fintype N] [DecidableEq N] in
@[simp] theorem matrixDerivative_apply (i : I)
    (x : Matrix N N (ScalarJetAlgebra.Algebra S I)) (a b : N) :
    matrixDerivative i x a b = ScalarJetAlgebra.totalDerivative i (x a b) := rfl

def matrixOrdinary : Ordinary I (Matrix N N (ScalarJetAlgebra.Algebra S I)) where
  d := matrixDerivative
  mul i x y := by
    apply Matrix.ext
    intro a b
    change ScalarJetAlgebra.totalDerivative i (∑ k, x a k * y k b) =
      (∑ k, ScalarJetAlgebra.totalDerivative i (x a k) * y k b) +
        ∑ k, x a k * ScalarJetAlgebra.totalDerivative i (y k b)
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [mul_comm, add_comm] using ScalarJetAlgebra.totalDerivative_mul i (x a k) (y k b)
  commute i j x := by
    apply Matrix.ext
    intro a b
    exact ScalarJetAlgebra.totalDerivative_commute i j (x a b)

def zeroOrdinary : Ordinary I (Matrix N N ℂ) where
  d := fun _ => 0
  mul _ _ _ := by simp
  commute _ _ _ := rfl

def noncommutingControl : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => if i = 0 then !![0, 1; 0, 0] else !![0, 0; 1, 0]

theorem curvature_control :
    curvature zeroOrdinary noncommutingControl 0 1 0 0 = 1 := by
  norm_num [curvature, zeroOrdinary, bracket, noncommutingControl, Matrix.mul_apply, Fin.sum_univ_two]

theorem curvature_control_nonzero : curvature zeroOrdinary noncommutingControl 0 1 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  rw [curvature_control] at this
  exact one_ne_zero this

end
end Math.FormalConnection
