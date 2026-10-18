import Math.RepresentationTheory.Multiplicity.IntertwinerTraceDuality
import Math.RepresentationTheory.Decomposition.ProductFactorization

/-! Residual-equivariant duality of multiplicities, via the perfect trace
pairing. Semisimplicity is needed only for the first-factor restriction. -/

namespace Math.MultiplicityDuality
noncomputable section
open Representation ProductFactorization SplitRepresentationProjection

variable {G H V U : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
  (tau : Representation ℂ (G × H) V) (r : Representation ℂ G U)

def restrictionDual : Equiv (firstRestriction tau.dual) (firstRestriction tau).dual where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext; intro phi
    apply LinearMap.ext; intro x
    change phi (tau (g⁻¹, (1 : H)⁻¹) x) = phi (tau (g⁻¹, 1) x)
    simp

def dualHomEquiv : MultiplicitySpace tau.dual r.dual ≃ₗ[ℂ]
    IntertwiningMap r.dual (firstRestriction tau).dual where
  toFun f := (restrictionDual tau).toIntertwiningMap.comp f
  invFun f := (restrictionDual tau).symm.toIntertwiningMap.comp f
  left_inv f := by ext phi x; rfl
  right_inv f := by ext phi x; rfl
  map_add' f g := by ext phi x; rfl
  map_smul' c f := by ext phi x; rfl

def reverseEquiv : MultiplicitySpace tau.dual r.dual ≃ₗ[ℂ]
    IntertwiningMap (firstRestriction tau) r :=
  (dualHomEquiv tau r).trans (IntertwinerTraceDuality.transposeEquiv (firstRestriction tau) r)

theorem reverse_apply (f : MultiplicitySpace tau.dual r.dual)
    (x : V) (phi : Module.Dual ℂ U) : phi (reverseEquiv tau r f x) = f phi x :=
  IntertwinerTraceDuality.transpose_apply (firstRestriction tau) r _ x phi

theorem reverse_action (h : H) (f : MultiplicitySpace tau.dual r.dual) (x : V) :
    reverseEquiv tau r (multiplicityRepresentation tau.dual r.dual h f) x =
      reverseEquiv tau r f (tau (1, h⁻¹) x) := by
  apply (Module.evalEquiv ℂ U).injective
  apply LinearMap.ext; intro phi
  change phi (reverseEquiv tau r (multiplicityRepresentation tau.dual r.dual h f) x) = _
  rw [reverse_apply]
  change f phi (tau ((1 : G)⁻¹, h⁻¹) x) = phi (reverseEquiv tau r f (tau (1, h⁻¹) x))
  rw [reverse_apply, inv_one]

variable [IsIrreducible r]

def equiv (hs : IsSemisimpleRepresentation (firstRestriction tau)) :
    Equiv (multiplicityRepresentation tau.dual r.dual)
      (multiplicityRepresentation tau r).dual where
  toLinearEquiv := (reverseEquiv tau r).trans
    (IntertwinerTraceDuality.equiv (firstRestriction tau) r hs)
  isIntertwining' h := by
    apply LinearMap.ext; intro f
    apply LinearMap.ext; intro g
    change LinearMap.trace ℂ U
      ((reverseEquiv tau r (multiplicityRepresentation tau.dual r.dual h f)).toLinearMap.comp
        g.toLinearMap) =
      LinearMap.trace ℂ U ((reverseEquiv tau r f).toLinearMap.comp
        (multiplicityRepresentation tau r h⁻¹ g).toLinearMap)
    congr 1
    apply LinearMap.ext; intro x
    exact reverse_action tau r h f (g x)

end
end Math.MultiplicityDuality
