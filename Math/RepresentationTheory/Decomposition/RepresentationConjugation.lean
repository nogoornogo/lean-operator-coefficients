import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Change of coordinates for a representation, retaining restriction
compatibility with a previously given action. -/

set_option autoImplicit false

namespace Math.RepresentationConjugation

noncomputable section

/-- Preserve the exact equivalence without repeatedly reducing its chosen
coordinate implementation during elaboration. -/
def sealEquiv {G V W : Type*} [Monoid G]
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
    (e : Representation.Equiv rho sigma) : {f : Representation.Equiv rho sigma // f = e} :=
  Classical.choice ⟨⟨e, rfl⟩⟩

variable {G K V W : Type*} [Monoid G] [Monoid K]
variable [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]

def pullback (e : V ≃ₗ[ℂ] W) (rho : Representation ℂ G W) : Representation ℂ G V :=
  e.symm.conjRingEquiv.toMonoidHom.comp rho

theorem pullback_apply (e : V ≃ₗ[ℂ] W) (rho : Representation ℂ G W) (g : G) (x : V) :
    pullback e rho g x = e.symm (rho g (e x)) := rfl

def equiv (e : V ≃ₗ[ℂ] W) (rho : Representation ℂ G W) :
    Representation.Equiv (pullback e rho) rho :=
  .mk e (by
    intro g
    apply LinearMap.ext; intro x
    change e (e.symm (rho g (e x))) = rho g (e x)
    exact e.apply_symm_apply _)

theorem restriction_of_eq {tau : Representation ℂ K V} {gamma : Representation ℂ K W}
    (e : Representation.Equiv tau gamma) (rho : Representation ℂ G W) (f : K →* G)
    (h : rho.comp f = gamma) : (pullback e.toLinearEquiv rho).comp f = tau := by
  apply MonoidHom.ext; intro g
  change e.toLinearEquiv.symm.conj (rho (f g)) = tau g
  have hg : rho (f g) = gamma g := DFunLike.congr_fun h g
  rw [hg]
  exact e.symm.conj_apply_self g

end

end Math.RepresentationConjugation
