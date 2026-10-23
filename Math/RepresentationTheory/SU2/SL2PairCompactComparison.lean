import Math.RepresentationTheory.SU2.SL2SymmetricSpan

/-! Independent compact comparison for two complex SL2 factors. -/
namespace Math.SL2PairCompactComparison
set_option autoImplicit false
noncomputable section
open Representation SL2SymmetricEmbeddings
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ (Group × Group) V)

def compact : (TauCeti.SU2 × TauCeti.SU2) →* Group × Group :=
  MonoidHom.prodMap compactInclusion compactInclusion

theorem fixed_iff (hl : SL2SymmetricSpan.Spanned (rho.comp (MonoidHom.inl Group Group)))
    (hr : SL2SymmetricSpan.Spanned (rho.comp (MonoidHom.inr Group Group)))
    (f : Module.Dual ℂ V) :
    (∀ g x, f (rho g x) = f x) ↔ ∀ u x, f (rho (compact u) x) = f x := by
  constructor
  · intro h u x; exact h _ x
  · intro h
    have hleft : ∀ g x, f (rho (g,1) x) = f x :=
      SL2SymmetricSpan.coefficient_fixed_of_compact _ hl f
        (by intro u x; exact h (u,1) x)
    have hright : ∀ g x, f (rho (1,g) x) = f x :=
      SL2SymmetricSpan.coefficient_fixed_of_compact _ hr f
        (by intro u x; exact h (1,u) x)
    intro g x
    have he : g = (g.1,1) * (1,g.2) := by simp
    rw [he,map_mul,Module.End.mul_apply,hleft,hright]

end
end Math.SL2PairCompactComparison
