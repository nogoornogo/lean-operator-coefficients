import Math.LieGroups.Matrix.MatrixLieGroupNormalizer
import Math.LieGroups.Matrix.LieNormalizerLocalLog
import Math.LieGroups.SpecialUnitary.SpecialUnitaryLocalLog

/-!
# Local matrix logarithms in special-unitary normalizers

Near zero, a single exponential detects the same infinitesimal conditions
as the all-time criterion. Near the group identity, the ambient logarithm
satisfies those conditions without extra certificates.
-/

set_option autoImplicit false

namespace Math.MatrixLieGroupNormalizer

noncomputable section

open NormedSpace Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (L : LieSubalgebra ℝ (Matrix n n ℂ))

theorem eventually_exp_mem_matrixCarrier_iff :
    ∀ᶠ X : Matrix n n ℂ in 𝓝 0,
      exp X ∈ matrixCarrier L ↔ X ∈ L.normalizer ∧ Xᴴ = -X ∧ Matrix.trace X = 0 := by
  have hL : IsClosed (L : Set (Matrix n n ℂ)) := L.toSubmodule.closed_of_finiteDimensional
  filter_upwards [LieNormalizerLocalLog.eventually_normalizes_of_exp_conjugate_mem L hL,
    SpecialUnitaryLocalLog.eventually_exp_mem_iff (n := n)] with X hn hs
  constructor
  · intro hX
    obtain ⟨hsk, ht⟩ := hs.mp (matrixCarrier_le_special L hX)
    refine ⟨hn ?_, hsk, ht⟩
    obtain ⟨g, hg, he⟩ := (mem_matrixCarrier L _).mp hX
    have hi : (↑(g⁻¹) : Matrix n n ℂ) = exp (-X) := by
      simpa only [one_smul] using inverse_coe_exp X hsk 1 g (by simpa using he)
    intro Y hY
    have hc := hg.1 Y hY
    change (g : Matrix n n ℂ) * Y * (↑(g⁻¹) : Matrix n n ℂ) ∈ L at hc
    rw [he, hi] at hc
    exact hc
  · intro hX
    simpa using (exp_mem_matrixCarrier_iff L X).mpr hX 1

/-- The ambient Banach-algebra logarithm, without asserting global inverse properties. -/
def localLog (g : subgroup L) : Matrix n n ℂ :=
  NormedSpace.log (g.val : Matrix n n ℂ)

@[simp] theorem localLog_one : localLog L 1 = 0 := by
  simp [localLog]

theorem localLog_tendsto : Tendsto (localLog L) (𝓝 1) (𝓝 0) := by
  have ht : Tendsto (fun g : subgroup L => (g.val : Matrix n n ℂ)) (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def, Subgroup.coe_one, Submonoid.coe_one] using
      (continuous_subtype_val.comp continuous_subtype_val).tendsto (1 : subgroup L)
  have hl : Tendsto (NormedSpace.log : Matrix n n ℂ → Matrix n n ℂ) (𝓝 1) (𝓝 0) := by
    simpa only [NormedSpace.log_one] using
      (analyticAt_log_one ℝ (Matrix n n ℂ)).continuousAt.tendsto
  exact hl.comp ht

theorem eventually_exp_localLog :
    ∀ᶠ g : subgroup L in 𝓝 1, exp (localLog L g) = (g.val : Matrix n n ℂ) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have ht : Tendsto (fun g : subgroup L => (g.val : Matrix n n ℂ)) (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def, Subgroup.coe_one, Submonoid.coe_one] using
      (continuous_subtype_val.comp continuous_subtype_val).tendsto (1 : subgroup L)
  exact ht.eventually (eventually_exp_log (Matrix n n ℂ))

theorem eventually_localLog_conditions :
    ∀ᶠ g : subgroup L in 𝓝 1,
      localLog L g ∈ L.normalizer ∧ (localLog L g)ᴴ = -localLog L g ∧
        Matrix.trace (localLog L g) = 0 := by
  filter_upwards [(localLog_tendsto L).eventually (eventually_exp_mem_matrixCarrier_iff L),
    eventually_exp_localLog L] with g hc he
  apply hc.mp
  rw [he]
  exact (mem_matrixCarrier L _).mpr ⟨g.val, g.property, rfl⟩

end

end Math.MatrixLieGroupNormalizer
