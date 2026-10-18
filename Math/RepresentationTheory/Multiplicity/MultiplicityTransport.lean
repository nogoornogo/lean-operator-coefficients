import Math.RepresentationTheory.Decomposition.ProductFactorization
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Multiplicities preserve equivariant equivalences and finite direct sums. -/

namespace Math.MultiplicityTransport
noncomputable section
open Representation ProductFactorization SplitRepresentationProjection

variable {G H V W U U' : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  {tau : Representation ℂ (G × H) V} {sigma : Representation ℂ (G × H) W}
  {r : Representation ℂ G U} {s : Representation ℂ G U'}

def target (e : Equiv tau sigma) (r : Representation ℂ G U) :
    Equiv (multiplicityRepresentation tau r) (multiplicityRepresentation sigma r) where
  toLinearEquiv := {
    toFun := fun f => (restrictEquiv e (MonoidHom.inl G H)).toIntertwiningMap.comp f
    invFun := fun f => (restrictEquiv e.symm (MonoidHom.inl G H)).toIntertwiningMap.comp f
    left_inv := by intro f; ext x; exact e.toLinearEquiv.symm_apply_apply (f x)
    right_inv := by intro f; ext x; exact e.toLinearEquiv.apply_symm_apply (f x)
    map_add' := by intro f g; ext x; exact map_add e (f x) (g x)
    map_smul' := by intro c f; ext x; exact map_smul e c (f x) }
  isIntertwining' h := by
    apply LinearMap.ext; intro f
    ext x
    exact e.toIntertwiningMap.isIntertwining _ _ (1, h) (f x)

def source (tau : Representation ℂ (G × H) V) (e : Equiv r s) :
    Equiv (multiplicityRepresentation tau r) (multiplicityRepresentation tau s) where
  toLinearEquiv := {
    toFun := fun f => f.comp e.symm.toIntertwiningMap
    invFun := fun f => f.comp e.toIntertwiningMap
    left_inv := by intro f; ext x; exact congrArg f (e.toLinearEquiv.symm_apply_apply x)
    right_inv := by intro f; ext x; exact congrArg f (e.toLinearEquiv.apply_symm_apply x)
    map_add' := by intro f g; ext x; rfl
    map_smul' := by intro c f; ext x; rfl }
  isIntertwining' h := by ext f x; rfl

def prod (tau : Representation ℂ (G × H) V) (sigma : Representation ℂ (G × H) W)
    (r : Representation ℂ G U) :
    Equiv (multiplicityRepresentation (tau.prod sigma) r)
      ((multiplicityRepresentation tau r).prod (multiplicityRepresentation sigma r)) where
  toLinearEquiv := {
    toFun := fun f =>
      ((IntertwiningMap.fst ℂ (firstRestriction tau) (firstRestriction sigma)).comp f,
       (IntertwiningMap.snd ℂ (firstRestriction tau) (firstRestriction sigma)).comp f)
    invFun := fun f => f.1.prod f.2
    left_inv := by intro f; ext x <;> rfl
    right_inv := by intro f; rfl
    map_add' := by intro f g; rfl
    map_smul' := by intro c f; rfl }
  isIntertwining' h := by ext f x <;> rfl

end
end Math.MultiplicityTransport
