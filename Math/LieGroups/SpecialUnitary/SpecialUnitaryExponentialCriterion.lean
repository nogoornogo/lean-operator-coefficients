import Math.LieGroups.Matrix.MatrixDeterminantExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Detecting the special-unitary matrix Lie algebra by exponential lines

All real times, not a single exponential, are required in the reverse direction.
-/

set_option autoImplicit false

namespace Math.SpecialUnitaryExponentialCriterion

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem skew_of_exp_mem (X : Matrix n n ℂ)
    (hX : ∀ t : ℝ, exp (t • X) ∈ Matrix.specialUnitaryGroup n ℂ) : Xᴴ = -X := by
  have he : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const X (0 : ℝ)
  have hunit : (fun t : ℝ => star (exp (t • X)) * exp (t • X)) = fun _ => 1 := by
    funext t
    exact (hX t).1.1
  have hd : HasDerivAt (fun t : ℝ => star (exp (t • X)) * exp (t • X))
      (star X * exp ((0 : ℝ) • X) + star (exp ((0 : ℝ) • X)) * X) 0 := he.star.mul he
  rw [hunit] at hd
  have hd' : HasDerivAt (fun _ : ℝ => (1 : Matrix n n ℂ)) (Xᴴ + X) 0 := by
    simpa only [zero_smul, exp_zero, star_one, mul_one, one_mul,
      Matrix.star_eq_conjTranspose] using hd
  exact eq_neg_of_add_eq_zero_left (hd'.unique (hasDerivAt_const 0 1))

theorem trace_zero_of_exp_mem (X : Matrix n n ℂ)
    (hX : ∀ t : ℝ, exp (t • X) ∈ Matrix.specialUnitaryGroup n ℂ) : Matrix.trace X = 0 := by
  have hd : HasDerivAt (fun t : ℝ => Matrix.det (exp (t • X))) (Matrix.trace X) 0 := by
    simpa only [Complex.ofReal_zero, Complex.coe_smul] using
      (MatrixDeterminantExponential.hasDerivAt_det_exp_smul_zero X).comp_ofReal
  have heq : (fun t : ℝ => Matrix.det (exp (t • X))) = fun _ => 1 := by
    funext t
    exact (hX t).2
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 1)

theorem exp_mem_iff (X : Matrix n n ℂ) :
    (∀ t : ℝ, exp (t • X) ∈ Matrix.specialUnitaryGroup n ℂ) ↔ Xᴴ = -X ∧ Matrix.trace X = 0 := by
  constructor
  · intro hX
    exact ⟨skew_of_exp_mem X hX, trace_zero_of_exp_mem X hX⟩
  · rintro ⟨hs, ht⟩ t
    let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    let : IsScalarTower ℚ ℂ (Matrix n n ℂ) := IsScalarTower.restrictScalars ℚ ℂ _
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · apply exp_mem_unitary_of_mem_skewAdjoint
      exact skewAdjoint.smul_mem t hs
    · rw [MatrixDeterminantExponential.det_exp, Matrix.trace_smul, ht, smul_zero, Complex.exp_zero]

end

end Math.SpecialUnitaryExponentialCriterion
