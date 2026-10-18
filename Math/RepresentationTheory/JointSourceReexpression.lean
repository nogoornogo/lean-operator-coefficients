import Math.RepresentationTheory.JointSourceData

/-! Put executable syntax in the outer field of an existing actual source
presentation. The representation equivalence is retained by an ordinary cast. -/
namespace Math.JointSourcePresentation
set_option autoImplicit false
open JointSourceExpression

noncomputable def reexpress {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {rho : Representation ℂ JointColorSpinWord.Group V}
    (p : Presentation rho) (e : Expr) (h : e=p.expression) : Presentation rho where
  expression := e
  equivalence := by rw [h]; exact p.equivalence

theorem reexpress_expression {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {rho : Representation ℂ JointColorSpinWord.Group V}
    (p : Presentation rho) (e : Expr) (h : e=p.expression) :
    (reexpress p e h).expression = e := rfl

end Math.JointSourcePresentation
