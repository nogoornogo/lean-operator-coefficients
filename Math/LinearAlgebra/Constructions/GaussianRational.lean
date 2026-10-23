import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Exact Gaussian rational arithmetic, using mathlib's quadratic algebra. -/
namespace Math.GaussianRational
set_option autoImplicit false
abbrev Scalar := QuadraticAlgebra ℚ (-1) 0

instance noRoot : Fact (∀ r : ℚ, r^2 ≠ (-1 : ℚ) + 0*r) := ⟨by
  intro r h
  have := sq_nonneg r
  norm_num at h
  linarith⟩

noncomputable def embed : Scalar →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp [Complex.I_mul_I]⟩

@[simp] theorem embed_apply (z : Scalar) : embed z = (z.re : ℂ) + (z.im : ℂ)*Complex.I := by
  simp [embed, QuadraticAlgebra.lift, Rat.smul_def]

theorem injective : Function.Injective embed := embed.injective

@[simp] theorem embed_star (z : Scalar) : embed (star z) = star (embed z) := by
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, mul_comm]

end Math.GaussianRational

namespace Math.GaussianRational
noncomputable section
open Matrix Polynomial
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def gramPolynomial (A : Matrix I J Scalar) : Scalar[X] := (Aᴴ*A).charpoly

omit [DecidableEq I] in
theorem gramPolynomial_map (A : Matrix I J Scalar) :
    (gramPolynomial A).map embed.toRingHom = ((A.map embed)ᴴ * A.map embed).charpoly := by
  rw [gramPolynomial, ← Matrix.charpoly_map]
  congr 1
  rw [Matrix.map_mul]
  congr 1
  ext i j
  exact embed_star _

theorem natTrailingDegree_map (p : Scalar[X]) :
    (p.map embed.toRingHom).natTrailingDegree = p.natTrailingDegree := by
  unfold Polynomial.natTrailingDegree Polynomial.trailingDegree
  rw [Polynomial.support_map_of_injective p injective]

end
end Math.GaussianRational
