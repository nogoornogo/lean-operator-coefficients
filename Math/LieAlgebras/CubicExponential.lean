import Math.LieAlgebras.SparseCubicCertificate
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Infinitesimally invariant cubic functions are invariant under matrix
exponentials. The proof differentiates the actual matrix orbit, not a
formal or truncated exponential. -/

set_option autoImplicit false

namespace Math.SparseCubicCertificate

noncomputable section

variable {n : Type*}
open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

theorem hasDerivAt_eval (p : Code n) (v : ℝ → n → ℂ) (w : n → ℂ) (t : ℝ)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (w i) t) :
    HasDerivAt (fun s => eval p (v s)) (differential p (v t) w) t := by
  induction p with
  | nil => exact hasDerivAt_const t 0
  | cons e es ih =>
    have h := ((((hv e.1.1).mul (hv e.1.2.1)).mul (hv e.1.2.2)).const_mul (e.2 : ℂ)).add ih
    convert h using 1 <;> try rfl
    · funext s; dsimp [eval, value]; ring
    · dsimp [differential]; ring

variable [Fintype n] [DecidableEq n]

theorem hasDerivAt_exp_mulVec (X : Matrix n n ℂ) (v : n → ℂ) (t : ℝ) (i : n) :
    HasDerivAt (fun s : ℝ => (exp (s • X) *ᵥ v) i)
      ((X *ᵥ (exp (t • X) *ᵥ v)) i) t := by
  have hd := hasDerivAt_exp_smul_const' X t
  have hi (j : n) := (hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j).mul_const (v j)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hi j)
  rw [Matrix.mulVec_mulVec]
  exact hs

theorem eval_exp_of_infinitesimal (p : Code n) (X : Matrix n n ℂ)
    (hX : ∀ v : n → ℂ, differential p v (X *ᵥ v) = 0) (v : n → ℂ) :
    eval p (exp X *ᵥ v) = eval p v := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => eval p (exp (s • X) *ᵥ v)) 0 t := by
    have h := hasDerivAt_eval p (fun s : ℝ => exp (s • X) *ᵥ v)
      (X *ᵥ (exp (t • X) *ᵥ v)) t (hasDerivAt_exp_mulVec X v t)
    rwa [hX] at h
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) (1 : ℝ) 0
  simpa using hc

end

end Math.SparseCubicCertificate
