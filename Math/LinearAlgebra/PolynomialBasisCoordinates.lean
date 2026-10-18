import Math.LinearAlgebra.BilinearSelectedPaths
import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial coordinates in finite bases with derived bilinear expansion. -/
namespace Math.PolynomialBasisCoordinates
set_option autoImplicit false
noncomputable section

variable {S J K U V D : Type*} [Fintype J] [Fintype K]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup D] [Module ℂ D]
  (bu : Module.Basis J ℂ U) (bv : Module.Basis K ℂ V)
  (p : J → MvPolynomial S ℂ) (q : K → MvPolynomial S ℂ)

def evaluate (x : S → ℂ) : U := ∑ j, MvPolynomial.eval x (p j) • bu j

omit [Fintype K] in
@[simp] theorem coordinate (x : S → ℂ) (j : J) :
    bu.repr (evaluate bu p x) j = MvPolynomial.eval x (p j) := by
  classical
  unfold evaluate
  rw [bu.repr_sum_self]

def weights (i : J × K) : MvPolynomial S ℂ := p i.1 * q i.2

theorem expansion (f : U →ₗ[ℂ] V →ₗ[ℂ] D) (x : S → ℂ) :
    f (evaluate bu p x) (evaluate bv q x) =
    WeightedSelectedPaths.synthesis (BilinearSelectedPaths.paths f bu bv)
      (fun y i => MvPolynomial.eval y (weights p q i)) x := by
  rw [BilinearSelectedPaths.expansion f bu bv]
  unfold WeightedSelectedPaths.synthesis
  apply Finset.sum_congr rfl
  intro i _
  simp [BilinearSelectedPaths.weights, weights]

end
end Math.PolynomialBasisCoordinates
