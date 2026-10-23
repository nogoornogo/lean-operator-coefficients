import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-! Exact quadratic elimination with values in a possibly noncommutative algebra.
The odd Majorana identity requires the stated anticommutation relations. -/
namespace Math.AlgebraValuedQuadraticElimination
set_option autoImplicit false
noncomputable section
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def pairedAction (m a b : k) (J K x y : R) : R :=
  m • (x * y) + a • (J * y) + b • (x * K)

def solution (m a : k) (J : R) : R := -(a / m) • J

theorem paired_shifted (m a b : k) (hm : m ≠ 0) (J K x y : R) :
    pairedAction m a b J K (x + solution m a J) (y + solution m b K) =
      m • (x * y) - (a * b / m) • (J * K) := by
  simp only [pairedAction, solution, add_mul, mul_add, smul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  have h₁ : m * (-(b / m)) = -b := by field_simp [hm]
  have h₂ : m * (-(a / m)) = -a := by field_simp [hm]
  have h₃ : m * (-(b / m) * -(a / m)) = a * b / m := by field_simp [hm]
  have h₄ : a * -(b / m) = -(a * b / m) := by ring
  have h₅ : b * -(a / m) = -(a * b / m) := by ring
  rw [h₁, h₂, h₃, h₄, h₅]
  module

theorem paired_on_shell (m a b : k) (hm : m ≠ 0) (J K : R) :
    pairedAction m a b J K (solution m a J) (solution m b K) =
      -(a * b / m) • (J * K) := by
  simpa [neg_smul] using paired_shifted m a b hm J K 0 0

theorem paired_stationary_variation (m a b t : k) (hm : m ≠ 0) (J K x y : R) :
    pairedAction m a b J K (t • x + solution m a J) (t • y + solution m b K) =
      -(a * b / m) • (J * K) + (t ^ 2 * m) • (x * y) := by
  rw [paired_shifted m a b hm]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : m * (t * t) = t ^ 2 * m := by ring
  rw [h]
  module

/-- The two-component Majorana half is absorbed into N0*N1: the antisymmetric
spin pairing of odd components is twice that product. -/
def majoranaAction (m g : k) (J₀ J₁ N₀ N₁ : R) : R :=
  -m • (N₀ * N₁) - g • (N₀ * J₁ - N₁ * J₀)

theorem majorana_shifted (m g : k) (hm : m ≠ 0) (J₀ J₁ N₀ N₁ : R)
    (hJJ : J₁ * J₀ = -(J₀ * J₁)) (hNJ : N₁ * J₀ = -(J₀ * N₁)) :
    majoranaAction m g J₀ J₁ (N₀ + solution m g J₀) (N₁ + solution m g J₁) =
      -m • (N₀ * N₁) + (g ^ 2 / m) • (J₀ * J₁) := by
  simp only [majoranaAction, solution, add_mul, mul_add, smul_add, smul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hJJ, hNJ]
  simp only [smul_neg]
  have h₁ : -m * -(g / m) = g := by field_simp [hm]
  have h₂ : -m * (-(g / m) * -(g / m)) = -(g ^ 2 / m) := by field_simp [hm]
  have h₃ : g * -(g / m) = -(g ^ 2 / m) := by ring
  rw [h₁, h₂, h₃]
  module

theorem majorana_on_shell (m g : k) (hm : m ≠ 0) (J₀ J₁ : R)
    (hJJ : J₁ * J₀ = -(J₀ * J₁)) :
    majoranaAction m g J₀ J₁ (solution m g J₀) (solution m g J₁) =
      (g ^ 2 / m) • (J₀ * J₁) := by
  simpa using majorana_shifted m g hm J₀ J₁ 0 0 hJJ (by simp)

/-- No term linear in the commuting variation parameter remains. -/
theorem majorana_stationary_variation (m g t : k) (hm : m ≠ 0) (J₀ J₁ N₀ N₁ : R)
    (hJJ : J₁ * J₀ = -(J₀ * J₁)) (hNJ : N₁ * J₀ = -(J₀ * N₁)) :
    majoranaAction m g J₀ J₁ (t • N₀ + solution m g J₀) (t • N₁ + solution m g J₁) =
      (g ^ 2 / m) • (J₀ * J₁) - (t ^ 2 * m) • (N₀ * N₁) := by
  rw [majorana_shifted m g hm _ _ _ _ hJJ
    (by simp only [smul_mul_assoc, mul_smul_comm, hNJ, smul_neg])]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : -m * (t * t) = -(t ^ 2 * m) := by ring
  rw [h]
  module

end
end Math.AlgebraValuedQuadraticElimination
