import Mathlib.LinearAlgebra.Trace
import Mathlib.Basic.Complex.Basic

/-! # Trace in an eigenbasis -/

namespace Math.WeightTheory
open scoped BigOperators

theorem trace_eq_sum_of_basis_eigen
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (f : V →ₗ[ℂ] V) (weightValue : ι -> ℂ)
    (hf : ∀ i, f (b i) = weightValue i • b i) :
    LinearMap.trace ℂ V f = ∑ i, weightValue i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b f]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [Matrix.diag, LinearMap.toMatrix_apply, hf, b.repr_self]

end Math.WeightTheory
