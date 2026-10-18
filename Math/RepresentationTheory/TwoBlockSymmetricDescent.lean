import Math.RepresentationTheory.SymmetricPowerDescent
import Math.RepresentationTheory.InvariantCoefficientTransport

/-! Independent symmetric block descent, with both inverse identities. -/
namespace Math.TwoBlockSymmetricDescent
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {B D X : Type*} [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup X] [Module ℂ X]

abbrev Nested (h d : ℕ) := SymmetricPowerDescent.symmetricMaps (A := B)
  (N := SymmetricPowerDescent.symmetricMaps (A := D) (N := ℂ) d) h

def value {h d : ℕ} (f : Nested (B := B) (D := D) h d) (v : Fin h → B) (w : Fin d → D) : ℂ :=
  (f.val v).val w

def equiv (h d : ℕ) : (Sym[ℂ]^h B ⊗[ℂ] Sym[ℂ]^d D →ₗ[ℂ] ℂ) ≃ₗ[ℂ] Nested (B := B) (D := D) h d :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) (Sym[ℂ]^h B) (Sym[ℂ]^d D) ℂ).symm.trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl ℂ (Sym[ℂ]^h B))
      (SymmetricPowerDescent.equiv d)).trans (SymmetricPowerDescent.equiv h))

@[simp] theorem equiv_apply (h d : ℕ) (f : Sym[ℂ]^h B ⊗[ℂ] Sym[ℂ]^d D →ₗ[ℂ] ℂ)
    (v : Fin h → B) (w : Fin d → D) :
    value (equiv h d f) v w = f (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) := rfl

@[simp] theorem lift_apply (h d : ℕ) (f : Nested (B := B) (D := D) h d)
    (v : Fin h → B) (w : Fin d → D) :
    (equiv h d).symm f (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) = value f v w := by
  simpa only [equiv_apply] using congrArg (fun k : Nested (B := B) (D := D) h d => value k v w)
    ((equiv h d).apply_symm_apply f)

def sourceEquiv (h d : ℕ) :
    (X ⊗[ℂ] (Sym[ℂ]^h B ⊗[ℂ] Sym[ℂ]^d D) →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      (X →ₗ[ℂ] Nested (B := B) (D := D) h d) :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) X (Sym[ℂ]^h B ⊗[ℂ] Sym[ℂ]^d D) ℂ).symm.trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl ℂ X) (equiv h d))

@[simp] theorem sourceEquiv_apply (h d : ℕ)
    (f : X ⊗[ℂ] (Sym[ℂ]^h B ⊗[ℂ] Sym[ℂ]^d D) →ₗ[ℂ] ℂ)
    (x : X) (v : Fin h → B) (w : Fin d → D) :
    value (sourceEquiv h d f x) v w =
      f (x ⊗ₜ[ℂ] (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)) := rfl

@[simp] theorem sourceLift_apply (h d : ℕ) (f : X →ₗ[ℂ] Nested (B := B) (D := D) h d)
    (x : X) (v : Fin h → B) (w : Fin d → D) :
    (sourceEquiv h d).symm f
      (x ⊗ₜ[ℂ] (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)) = value (f x) v w := by
  simpa only [sourceEquiv_apply] using congrArg
    (fun k : X →ₗ[ℂ] Nested (B := B) (D := D) h d => value (k x) v w)
      ((sourceEquiv h d).apply_symm_apply f)

variable {G : Type*} [Group G] (a : Representation ℂ G X)
  (b : Representation ℂ G B) (c : Representation ℂ G D)

def ordered (h d : ℕ) : Submodule ℂ (X →ₗ[ℂ] Nested (B := B) (D := D) h d) where
  carrier := {f | ∀ g x v w, value (f (a g x)) (fun i => b g (v i)) (fun j => c g (w j)) = value (f x) v w}
  zero_mem' := by intro g x v w; rfl
  add_mem' := by intro f k hf hk g x v w; change value (f _) _ _ + value (k _) _ _ = _; rw [hf,hk]; rfl
  smul_mem' := by intro z f hf g x v w; change z • value (f _) _ _ = _; rw [hf]; rfl

abbrev Coefficients (h d : ℕ) := InvariantCoefficientTransport.Invariants
  (a.tprod ((b.symmetricPower h).tprod (c.symmetricPower d)))

def extract (h d : ℕ) (f : Coefficients a b c h d) : ordered a b c h d :=
  ⟨sourceEquiv h d f.toLinearMap, by
    intro g x v w
    have he := IntertwiningMap.isIntertwining _ _ f g
      (x ⊗ₜ[ℂ] (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))
    change f (a g x ⊗ₜ[ℂ] (b.symmetricPower h g (SymmetricPower.tprod ℂ v) ⊗ₜ[ℂ]
      c.symmetricPower d g (SymmetricPower.tprod ℂ w))) =
        f (x ⊗ₜ[ℂ] (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)) at he
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod] at he
    exact he⟩

def descend (h d : ℕ) (f : ordered a b c h d) : Coefficients a b c h d where
  toLinearMap := (sourceEquiv h d).symm f.val
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply TensorProduct.ext
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin h) B)
    rintro _ ⟨v,rfl⟩
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin d) D)
    rintro _ ⟨w,rfl⟩
    change (sourceEquiv h d).symm f.val
      (a g x ⊗ₜ[ℂ] (b.symmetricPower h g (SymmetricPower.tprod ℂ v) ⊗ₜ[ℂ]
        c.symmetricPower d g (SymmetricPower.tprod ℂ w))) =
      (sourceEquiv h d).symm f.val (x ⊗ₜ[ℂ]
        (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod,
      sourceLift_apply,sourceLift_apply]
    exact f.property g x v w

def coefficientEquiv (h d : ℕ) : Coefficients a b c h d ≃ₗ[ℂ] ordered a b c h d where
  toFun := extract a b c h d
  invFun := descend a b c h d
  left_inv f := by apply IntertwiningMap.ext; exact (sourceEquiv h d).symm_apply_apply f.toLinearMap
  right_inv f := by apply Subtype.ext; exact (sourceEquiv h d).apply_symm_apply f.val
  map_add' f k := by apply Subtype.ext; exact (sourceEquiv h d).map_add _ _
  map_smul' z f := by apply Subtype.ext; exact (sourceEquiv h d).map_smul _ _

end
end Math.TwoBlockSymmetricDescent
