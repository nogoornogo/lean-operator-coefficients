import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-! Exact elimination of a paired quadratic form. The bilinear form need
not be positive definite or symmetric; no path integral is assumed. -/

set_option autoImplicit false
namespace Math.PairedQuadraticElimination

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

def action (B : E →ₗ[k] E →ₗ[k] k) (m g : k) (J K x y : E) : k :=
  m * B x y + g * (B J y + B x K)

def solution (m g : k) (J : E) : E := -(g / m) • J

theorem shifted_action (B : E →ₗ[k] E →ₗ[k] k) (m g : k) (hm : m ≠ 0)
    (J K x y : E) :
    action B m g J K (x + solution m g J) (y + solution m g K) =
      m * B x y - g ^ 2 / m * B J K := by
  simp [action, solution, map_add, map_smul, smul_eq_mul]
  field_simp
  ring

theorem on_shell (B : E →ₗ[k] E →ₗ[k] k) (m g : k) (hm : m ≠ 0) (J K : E) :
    action B m g J K (solution m g J) (solution m g K) =
      -(g ^ 2 / m) * B J K := by
  simpa using shifted_action B m g hm J K 0 0

/-- The shifted action has no term of first order in simultaneous variations. -/
theorem stationary_variation (B : E →ₗ[k] E →ₗ[k] k)
    (m g : k) (hm : m ≠ 0) (J K u v : E) (t : k) :
    action B m g J K (t • u + solution m g J) (t • v + solution m g K) =
      action B m g J K (solution m g J) (solution m g K) +
        t ^ 2 * m * B u v := by
  rw [shifted_action B m g hm, on_shell B m g hm]
  simp [map_smul, smul_eq_mul]
  ring

theorem source_equation (m g : k) (hm : m ≠ 0) (J : E) :
    m • solution m g J + g • J = 0 := by
  simp [solution, smul_smul, mul_div_cancel₀ g hm]

end Math.PairedQuadraticElimination
