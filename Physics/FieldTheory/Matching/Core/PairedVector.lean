import Math.LinearAlgebra.Constructions.PairedQuadraticElimination
import Physics.FieldTheory.Spinor.Weyl.WeylSpinor

open Math

/-! A complexified two-spinor vector pairing and local paired-field
elimination. The normalization is fixed explicitly by the epsilon tensors. -/

set_option autoImplicit false
namespace Physics.PairedVector
noncomputable section
open SMEpsilonTensor

abbrev Vector := Fin 2 → Fin 2 → ℂ

def rankOne (s u : WeylSpinor.Space) : Vector := fun i j => s i * u j

def pair (x y : Vector) : ℂ :=
  x 0 0 * y 1 1 - x 0 1 * y 1 0 - x 1 0 * y 0 1 + x 1 1 * y 0 0

def pairing : Vector →ₗ[ℂ] Vector →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ pair
    (by intros; simp [pair]; ring) (by intros; simp [pair]; ring)
    (by intros; simp [pair]; ring) (by intros; simp [pair]; ring)

theorem pairing_rankOne (s t u v : WeylSpinor.Space) :
    pairing (rankOne s u) (rankOne t v) = eps2 s t * eps2 u v := by
  change pair _ _ = _
  simp [pair, rankOne, eps2]
  ring

theorem pairing_symmetric (x y : Vector) : pairing x y = pairing y x := by
  change pair x y = pair y x
  simp [pair]
  ring

theorem pairing_nondegenerate (x : Vector) (h : ∀ y, pairing x y = 0) : x = 0 := by
  ext i j
  have h00 := h (rankOne (weakBasis 1) (weakBasis 1))
  have h01 := h (rankOne (weakBasis 1) (weakBasis 0))
  have h10 := h (rankOne (weakBasis 0) (weakBasis 1))
  have h11 := h (rankOne (weakBasis 0) (weakBasis 0))
  change pair x _ = 0 at h00 h01 h10 h11
  simp [pair, rankOne, weakBasis] at h00 h01 h10 h11
  fin_cases i <;> fin_cases j <;> assumption

theorem eliminate (m g : ℂ) (hm : m ≠ 0) (J K : Vector) :
    PairedQuadraticElimination.action pairing m g J K
      (PairedQuadraticElimination.solution m g J)
      (PairedQuadraticElimination.solution m g K) = -(g ^ 2 / m) * pairing J K :=
  PairedQuadraticElimination.on_shell pairing m g hm J K

end
end Physics.PairedVector
