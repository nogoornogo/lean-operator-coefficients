import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! The double commutator with a diagonal background, without a chosen
gauge group or dimension. -/

set_option autoImplicit false
namespace Math.DiagonalAdjointMass

variable {n k : Type*} [Fintype n] [DecidableEq n] [CommRing k]

def operator (d : n → k) (X : Matrix n n k) : Matrix n n k :=
  let D := Matrix.diagonal d
  D * (D * X - X * D) - (D * X - X * D) * D

theorem entry (d : n → k) (X : Matrix n n k) (i j : n) :
    operator d X i j = (d i - d j) ^ 2 * X i j := by
  simp [operator, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem single_eigenvector (d : n → k) (i j : n) (a : k) :
    operator d (Matrix.single i j a) = (d i - d j) ^ 2 • Matrix.single i j a := by
  ext r s
  by_cases hi : i = r <;> by_cases hj : j = s <;>
    simp_all [entry, Matrix.smul_apply, smul_eq_mul]

theorem diagonal_kernel (d a : n → k) : operator d (Matrix.diagonal a) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [entry, h]

end Math.DiagonalAdjointMass
