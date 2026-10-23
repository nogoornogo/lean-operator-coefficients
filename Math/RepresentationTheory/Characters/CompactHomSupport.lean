import Math.RepresentationTheory.Characters.CompactHomDimension
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Compact continuous Hom support is symmetric, without evaluating a character integral. -/
namespace Math.CompactHomSupport
set_option autoImplicit false
noncomputable section
open MeasureTheory Representation ContinuousRepresentationScope
variable {G V W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem dimension_symm (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) :
    Module.finrank ℂ (IntertwiningMap rho sigma) =
      Module.finrank ℂ (IntertwiningMap sigma rho) := by
  have he : (Module.finrank ℂ (IntertwiningMap rho sigma) : ℂ) =
      (Module.finrank ℂ (IntertwiningMap sigma rho) : ℂ) := by
    rw [← CompactHomDimension.integral_character_mul_eq_finrank rho sigma hr hs,
      ← CompactHomDimension.integral_character_mul_eq_finrank sigma rho hs hr]
    have hi := integral_inv_eq_self
      (fun g : G => rho.character g⁻¹ * sigma.character g) (TauCeti.haarProb G)
    simpa only [inv_inv, mul_comm] using hi.symm
  exact_mod_cast he

theorem nonzero_iff (rho : Representation ℂ G V) (sigma : Representation ℂ G W)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma) :
    SelectionCriteria.Allowed (IntertwiningMap rho sigma) ↔
      SelectionCriteria.Allowed (IntertwiningMap sigma rho) := by
  change (∃ f : IntertwiningMap rho sigma, f ≠ 0) ↔
    ∃ f : IntertwiningMap sigma rho, f ≠ 0
  rw [← Module.finrank_pos_iff_exists_ne_zero (R := ℂ),
    ← Module.finrank_pos_iff_exists_ne_zero (R := ℂ),
    dimension_symm rho sigma hr hs]

end
end Math.CompactHomSupport
