import Physics.StandardModel.Gauge.StandardSMIrreducibility

open Math

/-! Fundamental color and weak factors remain irreducible at any hypercharge. -/
set_option autoImplicit false
namespace GUT.StandardSMIrreducibility
noncomputable section
open Representation StandardSMGaugeTensor SmallSpecialUnitary

private def weakInclusion : Matrix.specialUnitaryGroup (Fin 2) ℂ →* GaugeGroup :=
  (MonoidHom.inr _ _).comp (MonoidHom.inl _ _)

theorem twisted_color_irreducible (n : ℤ) : (twist color n).IsIrreducible := by
  have he : (twist color n).comp (MonoidHom.inl _ _) = defining 3 := by
    ext g v
    simp [twist, phase, color, defining]
  have : IsIrreducible ((twist color n).comp (MonoidHom.inl _ _)) :=
    he.symm ▸ defining_three_irreducible
  exact Math.RepresentationTheory.isIrreducible_of_comp _ (MonoidHom.inl _ _)

theorem twisted_weak_irreducible (n : ℤ) : (twist weak n).IsIrreducible := by
  have he : (twist weak n).comp weakInclusion = defining 2 := by
    ext g v
    simp [twist, phase, weakInclusion, weak, defining]
  have : IsIrreducible ((twist weak n).comp weakInclusion) :=
    he.symm ▸ defining_two_irreducible
  exact Math.RepresentationTheory.isIrreducible_of_comp _ weakInclusion

theorem twisted_color_dual_irreducible (n : ℤ) : (twist color n).dual.IsIrreducible := by
  let : IsIrreducible (twist color n) := twisted_color_irreducible n
  exact Math.RepresentationTheory.dual_isIrreducible _

theorem twisted_weak_dual_irreducible (n : ℤ) : (twist weak n).dual.IsIrreducible := by
  let : IsIrreducible (twist weak n) := twisted_weak_irreducible n
  exact Math.RepresentationTheory.dual_isIrreducible _

theorem neutral_extension_irreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ GaugeGroup V) [rho.IsIrreducible]
    (H : Type*) [Group H] : IsIrreducible (rho.comp (MonoidHom.fst GaugeGroup H)) := by
  have he : (rho.comp (MonoidHom.fst GaugeGroup H)).comp (MonoidHom.inl _ _) = rho := rfl
  have : IsIrreducible ((rho.comp (MonoidHom.fst GaugeGroup H)).comp (MonoidHom.inl _ _)) :=
    he.symm ▸ (inferInstance : rho.IsIrreducible)
  exact Math.RepresentationTheory.isIrreducible_of_comp _ (MonoidHom.inl _ _)

end
end GUT.StandardSMIrreducibility
