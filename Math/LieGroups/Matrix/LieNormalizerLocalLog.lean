import Math.LieGroups.Matrix.LieNormalizerExponential
import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Inverse

/-!
# A local converse to preservation by exponential conjugation

The neighborhood hypothesis is essential. The proof applies the operator
logarithm to the commutator exponential on a closed invariant subspace.
-/

set_option autoImplicit false

namespace Math.LieNormalizerLocalLog

noncomputable section

open NormedSpace Filter
open scoped Topology

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem logOneAdd_apply_mem (S : Submodule ℝ R) (hS : IsClosed (S : Set R))
    (T : R →L[ℝ] R) (hT : ∀ y ∈ S, T y ∈ S) (hnorm : ‖T‖ < 1)
    (y : R) (hy : y ∈ S) : logOneAdd ℝ (R →L[ℝ] R) T y ∈ S := by
  have hp : ∀ n : ℕ, (T ^ n) y ∈ S := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact hT _ ih
  have hsum := (ContinuousLinearMap.apply ℝ R y).hasSum
    (summable_logOneAdd ℝ (R →L[ℝ] R) hnorm).hasSum
  rw [← logOneAdd_eq_tsum] at hsum
  apply hS.mem_of_tendsto hsum.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply S.sum_mem
  intro i _
  simpa only [map_smul, ContinuousLinearMap.apply_apply] using S.smul_mem _ (hp i)

theorem eventually_invariant_of_exp_invariant (S : Submodule ℝ R) (hS : IsClosed (S : Set R)) :
    ∀ᶠ T : R →L[ℝ] R in 𝓝 0,
      (∀ y ∈ S, exp T y ∈ S) → ∀ y ∈ S, T y ∈ S := by
  let : NormedAlgebra ℚ (R →L[ℝ] R) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hn : Tendsto (fun T : R →L[ℝ] R => ‖exp T - 1‖) (𝓝 0) (𝓝 0) := by
    simpa using (exp_continuous.sub (continuous_const (y := (1 : R →L[ℝ] R)))).norm.tendsto
      (0 : R →L[ℝ] R)
  filter_upwards [eventually_logOneAdd_exp_sub_one ℝ (R →L[ℝ] R),
    (tendsto_order.mp hn).2 1 zero_lt_one] with T hlog hnorm hT
  intro y hy
  have hinv : ∀ y ∈ S, (exp T - 1) y ∈ S := by
    intro y hy
    exact S.sub_mem (hT y hy) hy
  have hm := logOneAdd_apply_mem S hS _ hinv hnorm y hy
  rw [hlog] at hm
  exact hm

attribute [local instance 100] LieRing.ofAssociativeRing

variable (L : LieSubalgebra ℝ R) (hL : IsClosed (L : Set R))

include hL

theorem eventually_normalizes_of_exp_conjugate_mem :
    ∀ᶠ X : R in 𝓝 0,
      (∀ Y ∈ L, exp X * Y * exp (-X) ∈ L) → X ∈ L.normalizer := by
  let ad : R →L[ℝ] R →L[ℝ] R := TauCeti.Lie.continuousCommutator
  have had : Tendsto ad (𝓝 0) (𝓝 0) := by simpa using ad.continuous.tendsto 0
  filter_upwards [had.eventually (eventually_invariant_of_exp_invariant L.toSubmodule hL)]
    with X hX hconj
  rw [LieSubalgebra.mem_normalizer_iff]
  apply hX
  intro y hy
  rw [TauCeti.Lie.exp_continuousCommutator_apply]
  exact hconj y hy

end

end Math.LieNormalizerLocalLog
