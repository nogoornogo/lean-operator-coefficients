import Math.LinearAlgebra.PairedQuadraticElimination

/-! Unequal source coefficients in exact derivative-free paired elimination. -/
namespace Math.TwoSourceQuadraticElimination
set_option autoImplicit false
variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

def action (B : E →ₗ[k] E →ₗ[k] k) (m a b : k) (J K x y : E) : k :=
  m * B x y + a * B J y + b * B x K

def leftSolution (m a : k) (J : E) := -(a / m) • J
def rightSolution (m b : k) (K : E) := -(b / m) • K

theorem shifted_action (B : E →ₗ[k] E →ₗ[k] k) (m a b : k) (hm : m ≠ 0)
    (J K x y : E) :
    action B m a b J K (x + leftSolution m a J) (y + rightSolution m b K) =
      m * B x y - (a * b / m) * B J K := by
  simp [action, leftSolution, rightSolution, map_add, map_smul, smul_eq_mul]
  field_simp
  ring

theorem on_shell (B : E →ₗ[k] E →ₗ[k] k) (m a b : k) (hm : m ≠ 0) (J K : E) :
    action B m a b J K (leftSolution m a J) (rightSolution m b K) =
      -(a * b / m) * B J K := by
  simpa using shifted_action B m a b hm J K 0 0

theorem stationary_variation (B : E →ₗ[k] E →ₗ[k] k)
    (m a b : k) (hm : m ≠ 0) (J K u v : E) (t : k) :
    action B m a b J K (t • u + leftSolution m a J)
      (t • v + rightSolution m b K) =
      action B m a b J K (leftSolution m a J) (rightSolution m b K) +
        t ^ 2 * m * B u v := by
  rw [shifted_action B m a b hm, on_shell B m a b hm]
  simp [map_smul, smul_eq_mul]
  ring
end Math.TwoSourceQuadraticElimination
