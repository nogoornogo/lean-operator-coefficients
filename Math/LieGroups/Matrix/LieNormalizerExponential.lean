import TauCeti.Geometry.Lie.Adjoint.OperatorExponential
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Exponential criterion for a closed Lie normalizer in a real Banach algebra

This is a matrix-compatible analytic statement, without constructing a Lie
group or a manifold structure on a closed subgroup.
-/

set_option autoImplicit false

namespace Math.LieNormalizerExponential

noncomputable section

open NormedSpace Filter
open scoped Topology

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem exp_apply_mem (S : Submodule ℝ R) (hS : IsClosed (S : Set R))
    (T : R →L[ℝ] R) (hT : ∀ y ∈ S, T y ∈ S) (y : R) (hy : y ∈ S) :
    exp T y ∈ S := by
  have hp : ∀ n : ℕ, (T ^ n) y ∈ S := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact hT _ ih
  have hsum := (ContinuousLinearMap.apply ℝ R y).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) T)
  apply hS.mem_of_tendsto hsum.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply S.sum_mem
  intro i _
  simpa only [map_smul, ContinuousLinearMap.apply_apply] using S.smul_mem _ (hp i)

theorem hasDerivAt_conjugation_zero (X Y : R) :
    HasDerivAt (fun t : ℝ => exp (t • X) * Y * exp (-(t • X))) (X * Y - Y * X) 0 := by
  have hp : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const X (0 : ℝ)
  have hn : HasDerivAt (fun t : ℝ => exp (-(t • X))) (-X) 0 := by
    simpa only [smul_neg, zero_smul, neg_zero, exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (-X) (0 : ℝ)
  simpa [sub_eq_add_neg, Pi.mul_def] using (hp.mul_const Y).mul hn

omit [CompleteSpace R] in
theorem derivative_mem (S : Submodule ℝ R) (hS : IsClosed (S : Set R))
    {f : ℝ → R} {f' : R} (hf : HasDerivAt f f' 0) (hmem : ∀ t, f t ∈ S) : f' ∈ S := by
  apply hS.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hf)
  apply Eventually.of_forall
  intro t
  rw [slope_def_module]
  exact S.smul_mem _ (S.sub_mem (hmem t) (hmem 0))

attribute [local instance 100] LieRing.ofAssociativeRing

variable (L : LieSubalgebra ℝ R) (hL : IsClosed (L : Set R))

include hL

theorem exp_conjugate_mem (X : R) (hX : X ∈ L.normalizer)
    (t : ℝ) (Y : R) (hY : Y ∈ L) : exp (t • X) * Y * exp (-(t • X)) ∈ L := by
  rw [← TauCeti.Lie.exp_continuousCommutator_apply]
  apply exp_apply_mem L.toSubmodule hL _ _ Y hY
  intro y hy
  change ⁅t • X, y⁆ ∈ L
  rw [smul_lie]
  exact L.smul_mem t ((L.mem_normalizer_iff X).mp hX y hy)

theorem normalizes_iff_exp_conjugate_mem (X : R) :
    X ∈ L.normalizer ↔ ∀ t : ℝ, ∀ Y ∈ L, exp (t • X) * Y * exp (-(t • X)) ∈ L := by
  constructor
  · exact exp_conjugate_mem L hL X
  · intro h
    rw [LieSubalgebra.mem_normalizer_iff]
    intro Y hY
    exact derivative_mem L.toSubmodule hL (hasDerivAt_conjugation_zero X Y)
      (fun t => h t Y hY)

end

end Math.LieNormalizerExponential
