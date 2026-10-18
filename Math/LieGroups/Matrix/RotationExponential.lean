import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact rotation exponentials in a real Banach algebra. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.RotationExponential

noncomputable section

open NormedSpace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def rotation (X : R) (t : ℝ) : R :=
  1 + Real.sin t • X + (1 - Real.cos t) • X ^ 2

theorem rotation_derivative (X : R) (hX : X ^ 3 = -X) (t : ℝ) :
    X * rotation X t = Real.cos t • X + Real.sin t • X ^ 2 := by
  have hc : X * X ^ 2 = -X := by simpa only [← pow_succ'] using hX
  unfold rotation
  rw [mul_add, mul_add, mul_one, mul_smul_comm, mul_smul_comm, hc]
  simp only [← pow_two, smul_neg, sub_smul, one_smul]
  abel

theorem hasDerivAt_rotation (X : R) (t : ℝ) :
    HasDerivAt (rotation X) (Real.cos t • X + Real.sin t • X ^ 2) t := by
  unfold rotation
  simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, neg_neg] using
    ((hasDerivAt_const t (1 : R)).add ((Real.hasDerivAt_sin t).smul_const X)).add
      (((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).smul_const (X ^ 2))

theorem exp_eq_rotation [CompleteSpace R] (X : R) (hX : X ^ 3 = -X) (t : ℝ) :
    exp (t • X) = rotation X t := by
  have hd (s : ℝ) :
      HasDerivAt (fun u : ℝ => exp (u • (-X)) * rotation X u) 0 s := by
    have h := (hasDerivAt_exp_smul_const (-X) s).mul (hasDerivAt_rotation X s)
    rw [← rotation_derivative X hX s] at h
    simpa only [Pi.mul_def, neg_mul, mul_neg, mul_assoc, neg_add_cancel] using h
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [zero_smul, exp_zero, rotation, Real.sin_zero, Real.cos_zero,
    sub_self, zero_smul, add_zero, one_mul] at he
  have hf := congrArg (fun z : R => exp (t • X) * z) he
  have hi : exp (t • X) * exp (-(t • X)) = 1 := by
    let := NormedAlgebra.restrictScalars ℚ ℝ R
    rw [← exp_add_of_commute (Commute.refl (t • X)).neg_right,
      add_neg_cancel, exp_zero]
  simpa only [rotation, ← mul_assoc, smul_neg, hi, one_mul, mul_one] using hf.symm

end

end Math.RotationExponential
