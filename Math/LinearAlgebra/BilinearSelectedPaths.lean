import Math.LinearAlgebra.WeightedSelectedPaths
import Mathlib.LinearAlgebra.Basis.Defs

/-! Finite paths derived from bilinear coupling spaces, not supplied separately. -/
namespace Math.BilinearSelectedPaths
set_option autoImplicit false
noncomputable section

variable {X Y D E J K Z : Type*} [Fintype J] [Fintype K]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
  (f : X →ₗ[ℂ] Y →ₗ[ℂ] D) (bx : Module.Basis J ℂ X) (by_ : Module.Basis K ℂ Y)

def paths (i : J × K) : D := f (bx i.1) (by_ i.2)
def weights (z : X × Y) (i : J × K) : ℂ := bx.repr z.1 i.1 * by_.repr z.2 i.2

theorem expansion (x : X) (y : Y) : f x y =
    WeightedSelectedPaths.synthesis (paths f bx by_) (weights bx by_) (x,y) := by
  classical
  conv_lhs => rw [← bx.sum_repr x, ← by_.sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul,
    WeightedSelectedPaths.synthesis, paths, weights, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [mul_comm]

omit [Fintype J] [Fintype K] in
theorem weights_isolate : WeightedSelectedPaths.Isolates (weights bx by_) := by
  classical
  intro i
  refine ⟨(bx i.1, by_ i.2), ?_, ?_⟩
  · simp [weights]
  · intro j hji
    by_cases hj : j.1 = i.1
    · have hk : j.2 ≠ i.2 := fun h => hji (Prod.ext hj h)
      simp [weights, hj, Ne.symm hk]
    · simp [weights, Ne.symm hj]

theorem exists_nonzero_iff_basis_path (P : D →ₗ[ℂ] E) :
    (∃ x y, P (f x y) ≠ 0) ↔ ∃ i : J × K, P (f (bx i.1) (by_ i.2)) ≠ 0 := by
  have h := WeightedSelectedPaths.exists_nonzero_iff_path P (paths f bx by_)
    (weights bx by_) (weights_isolate bx by_)
  simpa only [← expansion, paths, Prod.exists] using h

/-- Nonlinear or correlated parameterizations still have an exact expansion;
the existence theorem above does not assert their reachability. -/
theorem parameterized_expansion (u : Z → X) (v : Z → Y) (z : Z) :
    f (u z) (v z) = WeightedSelectedPaths.synthesis (paths f bx by_)
      (fun t => weights bx by_ (u t, v t)) z := expansion f bx by_ (u z) (v z)

end
end Math.BilinearSelectedPaths
