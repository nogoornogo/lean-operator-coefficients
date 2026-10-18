import Physics.StandardModel.Operators.QqueSpinorExterior

/-! A named physical endpoint keeps model-dependent field carriers opaque
while expressing exactly the existing nonzero exterior coefficient claim. -/
namespace GUT.PhysicalQqueEndpoint
set_option autoImplicit false
noncomputable section
open Representation
variable {K Q U E : Type*} [Group K]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ K Q) (u : Representation ℂ K U) (e : Representation ℂ K E)

def HasExterior : Prop := ∃ f : QqueSpinorExterior.ExteriorCoefficient q u e, f ≠ 0

theorem of_alternation (h : QqueSpinorExterior.HasNonzeroAlternation q u e) :
    HasExterior q u e := h.exists_exterior

theorem of_exists (h : ∃ f : QqueSpinorExterior.ExteriorCoefficient q u e, f ≠ 0) :
    HasExterior q u e := h

end
end GUT.PhysicalQqueEndpoint
