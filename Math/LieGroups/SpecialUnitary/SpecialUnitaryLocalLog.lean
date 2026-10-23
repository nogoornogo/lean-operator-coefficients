import Math.LieGroups.SpecialUnitary.SpecialUnitaryExponentialCriterion
import TauCeti.Analysis.Normed.Algebra.Logarithm.Inverse

/-!
# Local exponential criterion for skew-Hermitian traceless matrices

Local logarithm identities remove the periodic ambiguities of exponentiation.
-/

set_option autoImplicit false

namespace Math.SpecialUnitaryLocalLog

noncomputable section

open NormedSpace Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exp_star_eq_exp_neg_of_unitary (X : Matrix n n ℂ)
    (hX : exp X ∈ Matrix.unitaryGroup n ℂ) : exp (star X) = exp (-X) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hi : exp X * exp (-X) = 1 := by
    rw [← exp_add_of_commute (Commute.refl X).neg_right, add_neg_cancel, exp_zero]
  calc
    exp (star X) = star (exp X) := (star_exp X).symm
    _ = star (exp X) * (exp X * exp (-X)) := by rw [hi, mul_one]
    _ = (star (exp X) * exp X) * exp (-X) := (mul_assoc _ _ _).symm
    _ = exp (-X) := by rw [hX.1, one_mul]

theorem eventually_skew_of_exp_unitary :
    ∀ᶠ X : Matrix n n ℂ in 𝓝 0, exp X ∈ Matrix.unitaryGroup n ℂ → Xᴴ = -X := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hs : Tendsto (star : Matrix n n ℂ → Matrix n n ℂ) (𝓝 0) (𝓝 0) := by
    simpa using continuous_star.tendsto (0 : Matrix n n ℂ)
  have hn : Tendsto (fun X : Matrix n n ℂ => -X) (𝓝 0) (𝓝 0) := by
    simpa using continuous_neg.tendsto (0 : Matrix n n ℂ)
  filter_upwards [hs.eventually (eventually_log_exp (Matrix n n ℂ)),
    hn.eventually (eventually_log_exp (Matrix n n ℂ))] with X hs hn hX
  change star X = -X
  rw [← hs, exp_star_eq_exp_neg_of_unitary X hX, hn]

theorem eventually_trace_zero_of_exp_special :
    ∀ᶠ X : Matrix n n ℂ in 𝓝 0,
      exp X ∈ Matrix.specialUnitaryGroup n ℂ → Matrix.trace X = 0 := by
  let : NormedAlgebra ℚ ℂ := NormedAlgebra.restrictScalars ℚ ℝ _
  have ht : Tendsto (Matrix.trace : Matrix n n ℂ → ℂ) (𝓝 0) (𝓝 0) := by
    simpa using continuous_id.matrix_trace.tendsto (0 : Matrix n n ℂ)
  filter_upwards [ht.eventually (eventually_log_exp ℂ)] with X hlog hX
  have he : exp (Matrix.trace X) = 1 := by
    rw [← Complex.exp_eq_exp_ℂ, ← MatrixDeterminantExponential.det_exp]
    exact hX.2
  rw [he, NormedSpace.log_one] at hlog
  exact hlog.symm

theorem eventually_exp_mem_iff :
    ∀ᶠ X : Matrix n n ℂ in 𝓝 0,
      exp X ∈ Matrix.specialUnitaryGroup n ℂ ↔ Xᴴ = -X ∧ Matrix.trace X = 0 := by
  filter_upwards [eventually_skew_of_exp_unitary (n := n),
    eventually_trace_zero_of_exp_special (n := n)] with X hs ht
  constructor
  · intro hX
    exact ⟨hs hX.1, ht hX⟩
  · intro hX
    simpa using (SpecialUnitaryExponentialCriterion.exp_mem_iff X).mpr hX 1

end

end Math.SpecialUnitaryLocalLog
