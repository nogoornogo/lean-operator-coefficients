import Math.LieGroups.Torus.CircleHomLattice
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tangents of integer circle homomorphisms

The complex coefficient curve underlying the power homomorphism
`z |-> z^n` has derivative `i*n` at the identity.  This is the analytic
coordinate calculation needed to connect the cocharacter lattice to the
anti-Hermitian centralizer.
-/

namespace Math
namespace CircleHomLattice

noncomputable section

/-- The complex-valued coefficient of the integer power circle along the
standard real exponential parameter. -/
def circlePowerCoefficientCurve (n : ℤ) (t : ℝ) : ℂ :=
  ((Circle.exp t ^ n : Circle) : ℂ)

theorem circlePowerCoefficientCurve_eq_cexp (n : ℤ) (t : ℝ) :
    circlePowerCoefficientCurve n t =
      Complex.exp ((((n : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [circlePowerCoefficientCurve, ← Circle.exp_intCast_mul,
    Circle.coe_exp]

/-- The tangent of `z |-> z^n` at the circle identity is `i*n`. -/
theorem hasDerivAt_circlePowerCoefficientCurve (n : ℤ) :
    HasDerivAt (circlePowerCoefficientCurve n)
      ((n : ℂ) * Complex.I) 0 := by
  have hReal : HasDerivAt (fun t : ℝ => (n : ℝ) * t) (n : ℝ) 0 :=
    hasDerivAt_const_mul (n : ℝ)
  have hComplex :
      HasDerivAt (fun t : ℝ => (((n : ℝ) * t : ℝ) : ℂ)) (n : ℂ) 0 :=
    hReal.ofReal_comp
  have hExp := (hComplex.mul_const Complex.I).cexp
  rw [show circlePowerCoefficientCurve n =
      (fun t : ℝ =>
        Complex.exp ((((n : ℝ) * t : ℝ) : ℂ) * Complex.I)) by
    funext t
    exact circlePowerCoefficientCurve_eq_cexp n t]
  simpa using hExp

end

end CircleHomLattice
end Math
