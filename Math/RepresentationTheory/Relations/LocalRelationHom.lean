import Math.RepresentationTheory.Relations.LocalCoinvariantHom
import Math.RepresentationTheory.Constructions.CommutingActionHom

/-! Invariant functionals with independently generated stable relations descend
through local coinvariants and then the images of those relations. -/
namespace Math.LocalRelationHom
set_option autoImplicit false
noncomputable section
open Representation
variable {k G H U W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (a : Representation k G U) (b : Representation k H U) (t : Representation k H W)
  (commutes : ∀ g h u, a g (b h u) = b h (a g u))
  (R : Submodule k U) (stable : ∀ h, R ≤ R.comap (b h))

def Input : Submodule k (LocalCoinvariantHom.invariantHom a b t) where
  carrier := {f | R ≤ LinearMap.ker f.val.toLinearMap}
  zero_mem' := by intro u hu; rfl
  add_mem' := by
    intro f q hf hq u hu
    change f.val.toLinearMap u + q.val.toLinearMap u = 0
    rw [hf hu, hq hu, add_zero]
  smul_mem' := by
    intro z f hf u hu
    change z • f.val.toLinearMap u = 0
    rw [hf hu, smul_zero]

abbrev image := R.map (LocalCoinvariantHom.relations a).mkQ

include stable in
theorem image_stable : ∀ h, image a R ≤
    (image a R).comap (LocalCoinvariantHom.quotient a b commutes h) := by
  intro h u hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact ⟨b h v, stable h hv, rfl⟩

def constrainedEquiv : Input a b t R ≃ₗ[k]
    RelationQuotient.vanishing (LocalCoinvariantHom.quotient a b commutes) t (image a R) where
  toFun f := ⟨LocalCoinvariantHom.equiv a b t commutes f.val, by
    rintro u ⟨v,hv,rfl⟩
    exact f.property hv⟩
  invFun f := ⟨(LocalCoinvariantHom.equiv a b t commutes).symm f.val, by
    intro u hu
    exact f.property ⟨u, hu, rfl⟩⟩
  left_inv f := by apply Subtype.ext; exact (LocalCoinvariantHom.equiv a b t commutes).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (LocalCoinvariantHom.equiv a b t commutes).apply_symm_apply f.val
  map_add' f q := by apply Subtype.ext; exact (LocalCoinvariantHom.equiv a b t commutes).map_add _ _
  map_smul' z f := by apply Subtype.ext; exact (LocalCoinvariantHom.equiv a b t commutes).map_smul z _

abbrev residual := (LocalCoinvariantHom.quotient a b commutes).quotient
  (image a R) (image_stable a b commutes R stable)

def equiv : Input a b t R ≃ₗ[k] IntertwiningMap (residual a b commutes R stable) t :=
  (constrainedEquiv a b t commutes R).trans
    (RelationQuotient.equiv (LocalCoinvariantHom.quotient a b commutes) t
      (image a R) (image_stable a b commutes R stable))

theorem equiv_mk (f : Input a b t R) (u : U) :
    equiv a b t commutes R stable f ((image a R).mkQ
      ((LocalCoinvariantHom.relations a).mkQ u)) = f.val.val u := rfl

def combinedEquiv : RelationQuotient.vanishing (CommutingActionHom.action a b commutes)
    (t.comp (MonoidHom.snd G H)) R ≃ₗ[k] Input a b t R where
  toFun f := ⟨CommutingActionHom.invariantEquiv a b t commutes f.val, f.property⟩
  invFun f := ⟨(CommutingActionHom.invariantEquiv a b t commutes).symm f.val, f.property⟩
  left_inv f := by apply Subtype.ext; exact (CommutingActionHom.invariantEquiv a b t commutes).symm_apply_apply f.val
  right_inv f := by apply Subtype.ext; exact (CommutingActionHom.invariantEquiv a b t commutes).apply_symm_apply f.val
  map_add' f q := by apply Subtype.ext; exact (CommutingActionHom.invariantEquiv a b t commutes).map_add _ _
  map_smul' z f := by apply Subtype.ext; exact (CommutingActionHom.invariantEquiv a b t commutes).map_smul z _

section Transport
variable {U' : Type*} [AddCommGroup U'] [Module k U']
  (a' : Representation k G U') {b' : Representation k H U'}
  (e : Representation.Equiv b b')
  (compatible : ∀ g u, e (a g u) = a' g (e u))

def alongEquiv : Input a b t R ≃ₗ[k] Input a' b' t (R.map e.toLinearMap) where
  toFun f := ⟨⟨f.val.val.comp e.symm.toIntertwiningMap, by
    intro g u
    change f.val.val (e.toLinearEquiv.symm (a' g u)) = f.val.val (e.toLinearEquiv.symm u)
    have hi : e.toLinearEquiv.symm (a' g u) = a g (e.toLinearEquiv.symm u) := by
      apply e.toLinearEquiv.injective
      rw [e.toLinearEquiv.apply_symm_apply]
      change a' g u = e (a g (e.toLinearEquiv.symm u))
      rw [compatible]
      exact congrArg (a' g) (e.toLinearEquiv.apply_symm_apply u).symm
    rw [hi, f.val.property]⟩, by
      rintro _ ⟨u, hu, rfl⟩
      change f.val.val.toLinearMap (e.toLinearEquiv.symm (e.toLinearEquiv u)) = 0
      rw [e.toLinearEquiv.symm_apply_apply]
      exact f.property hu⟩
  invFun f := ⟨⟨f.val.val.comp e.toIntertwiningMap, by
    intro g u
    change f.val.val (e (a g u)) = f.val.val (e u)
    rw [compatible, f.val.property]⟩, by
      intro u hu
      exact f.property ⟨u, hu, rfl⟩⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    ext u
    exact congrArg f.val.val (e.toLinearEquiv.symm_apply_apply u)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    ext u
    exact congrArg f.val.val (e.toLinearEquiv.apply_symm_apply u)
  map_add' f q := by apply Subtype.ext; apply Subtype.ext; ext u; rfl
  map_smul' z f := by apply Subtype.ext; apply Subtype.ext; ext u; rfl
end Transport

end
end Math.LocalRelationHom
