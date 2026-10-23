import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.Basic

/-! Unit normalization of a supplied kinetic norm and invertible coefficient transport.
No mass spectrum, kinetic action, or nonzero restriction along an injection is inferred. -/
namespace Math.LightLineNormalization
set_option autoImplicit false
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [AddCommGroup F] [Module ℂ F]

def scale (z : E) : ℂ := (‖z‖⁻¹ : ℝ)
def unit (z : E) : E := scale z • z

omit [InnerProductSpace ℂ E] in
theorem scale_ne_zero (z : E) (hz : z ≠ 0) : scale z ≠ 0 := by
  simp [scale, norm_ne_zero_iff.mpr hz]

theorem unit_norm (z : E) (hz : z ≠ 0) : ‖unit z‖ = 1 := by
  simp [unit, scale, norm_smul, norm_ne_zero_iff.mpr hz]

theorem unit_mem_kernel (a : E →ₗ[ℂ] F) (z : E) (hz : a z = 0) : a (unit z) = 0 := by
  simp [unit, map_smul, hz]

theorem normalized_value (f : E →ₗ[ℂ] ℂ) (z : E) :
    f (unit z) = scale z * f z := by simp [unit]

theorem normalized_value_ne_zero_iff (f : E →ₗ[ℂ] ℂ) (z : E) (hz : z ≠ 0) :
    f (unit z) ≠ 0 ↔ f z ≠ 0 := by
  rw [normalized_value, mul_ne_zero_iff]
  simp [scale_ne_zero z hz]

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {n : ℕ}

theorem comp_equiv_ne_zero_iff (f : V [⋀^Fin n]→ₗ[ℂ] ℂ) (e : W ≃ₗ[ℂ] V) :
    f.compLinearMap e.toLinearMap ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro h hf
    subst f
    exact h (by ext v; rfl)
  · intro h hf
    apply h
    ext v
    have hv := DFunLike.congr_fun hf (fun i => e.symm (v i))
    simpa using hv

end
end Math.LightLineNormalization
