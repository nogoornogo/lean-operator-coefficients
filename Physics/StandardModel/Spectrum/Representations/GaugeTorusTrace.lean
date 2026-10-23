import Physics.StandardModel.Gauge.Charges.PhysicalTorus
import Mathlib.RepresentationTheory.Character

open Math

/-! Actual SM gauge traces on physical torus coordinates. The existing
namespace is retained for compatibility; no UV representation is assumed. -/

set_option autoImplicit false
namespace Physics.SU5.TorusMatterCharacter
open Math.SU5
noncomputable section
open StandardSMGaugeTensor

theorem character_prod {K V W : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (r : Representation ℂ K V) (s : Representation ℂ K W) (g : K) :
    (r.prod s).character g = r.character g + s.character g :=
  LinearMap.trace_prodMap' (r g) (s g)

theorem character_twist {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (r : Representation ℂ GaugeGroup V) (y : ℤ) (g : GaugeGroup) :
    (twist r y).character g = phase y g * r.character g := by
  change LinearMap.trace ℂ V (phase y g • r g) = _
  rw [map_smul]
  rfl

theorem color_character (z : PhysicalTorus.Coordinates) :
    color.character (PhysicalTorus.gaugePoint z) = (z 0 : ℂ) + (z 1 : ℂ) +
      ((z 0 : ℂ) * (z 1 : ℂ))⁻¹ := by
  simp [Representation.character, color, PhysicalTorus.gaugePoint, PhysicalTorus.color,
    MaximalTorus.diagonalElement, Matrix.trace, Fin.sum_univ_succ, add_assoc]

theorem color_character_inv (z : PhysicalTorus.Coordinates) :
    color.character (PhysicalTorus.gaugePoint z)⁻¹ = (z 0 : ℂ)⁻¹ + (z 1 : ℂ)⁻¹ +
      (z 0 : ℂ) * (z 1 : ℂ) := by
  change LinearMap.trace ℂ _ (Matrix.toLin' (star (Matrix.diagonal
    (fun i => (![z 0, z 1, (z 0 * z 1)⁻¹] i : ℂ))))) = _
  simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.trace,
    Fin.sum_univ_succ, ← Circle.coe_inv_eq_conj, add_assoc]

theorem weak_character (z : PhysicalTorus.Coordinates) :
    weak.character (PhysicalTorus.gaugePoint z) = (z 2 : ℂ) + (z 2 : ℂ)⁻¹ := by
  simp [Representation.character, weak, PhysicalTorus.gaugePoint, PhysicalTorus.weak,
    MaximalTorus.diagonalElement, Matrix.trace, Fin.sum_univ_succ]

theorem weak_character_inv (z : PhysicalTorus.Coordinates) :
    weak.character (PhysicalTorus.gaugePoint z)⁻¹ = (z 2 : ℂ)⁻¹ + (z 2 : ℂ) := by
  change LinearMap.trace ℂ _ (Matrix.toLin' (star (Matrix.diagonal
    (fun i => (![z 2, (z 2)⁻¹] i : ℂ))))) = _
  simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.trace,
    Fin.sum_univ_succ, ← Circle.coe_inv_eq_conj]

end
end Physics.SU5.TorusMatterCharacter
