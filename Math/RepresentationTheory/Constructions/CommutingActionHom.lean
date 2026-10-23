import Math.RepresentationTheory.Relations.LocalCoinvariantHom

/-! Product-group invariant coefficients descend to residual Hom on local
coinvariants. The target local action is trivial. -/
namespace Math.CommutingActionHom
set_option autoImplicit false
noncomputable section
open Representation
variable {k G H U W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (a : Representation k G U) (b : Representation k H U) (t : Representation k H W)
  (commutes : ∀ g h u, a g (b h u) = b h (a g u))

def action : Representation k (G × H) U where
  toFun p := a p.1 * b p.2
  map_one' := by simp
  map_mul' p q := by
    ext u
    change a (p.1 * q.1) (b (p.2 * q.2) u) = a p.1 (b p.2 (a q.1 (b q.2 u)))
    simp only [map_mul, Module.End.mul_apply]
    rw [commutes]

@[simp] theorem action_apply (g : G) (h : H) (u : U) :
    action a b commutes (g,h) u = a g (b h u) := rfl

def restrict (f : IntertwiningMap (action a b commutes) (t.comp (MonoidHom.snd G H))) :
    LocalCoinvariantHom.invariantHom a b t :=
  ⟨{ toLinearMap := f.toLinearMap
     isIntertwining' h := by
       apply LinearMap.ext
       intro u
       have he := IntertwiningMap.isIntertwining _ _ f (1,h) u
       simpa [action] using he }, by
    intro g u
    have he := IntertwiningMap.isIntertwining _ _ f (g,1) u
    simpa [action] using he⟩

def extend (f : LocalCoinvariantHom.invariantHom a b t) :
    IntertwiningMap (action a b commutes) (t.comp (MonoidHom.snd G H)) where
  toLinearMap := f.val.toLinearMap
  isIntertwining' p := by
    apply LinearMap.ext
    intro u
    change f.val (a p.1 (b p.2 u)) = t p.2 (f.val u)
    rw [f.property]
    exact IntertwiningMap.isIntertwining _ _ f.val p.2 u

def invariantEquiv : IntertwiningMap (action a b commutes) (t.comp (MonoidHom.snd G H)) ≃ₗ[k]
    LocalCoinvariantHom.invariantHom a b t where
  toFun := restrict a b t commutes
  invFun := extend a b t commutes
  left_inv f := by ext u; rfl
  right_inv f := by apply Subtype.ext; ext u; rfl
  map_add' f q := by apply Subtype.ext; ext u; rfl
  map_smul' z f := by apply Subtype.ext; ext u; rfl

def equiv : IntertwiningMap (action a b commutes) (t.comp (MonoidHom.snd G H)) ≃ₗ[k]
    IntertwiningMap (LocalCoinvariantHom.quotient a b commutes) t :=
  (invariantEquiv a b t commutes).trans (LocalCoinvariantHom.equiv a b t commutes)

@[simp] theorem equiv_mk
    (f : IntertwiningMap (action a b commutes) (t.comp (MonoidHom.snd G H))) (u : U) :
    equiv a b t commutes f ((LocalCoinvariantHom.relations a).mkQ u) = f u := rfl

end
end Math.CommutingActionHom
