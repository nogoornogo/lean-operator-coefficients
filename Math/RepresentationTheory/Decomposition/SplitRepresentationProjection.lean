import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Basic.Complex.Basic

/-!
# Split projections, contragredients, and biduals of representations

Explicit equivariant retractions let a nonzero tensor on identified field
representations be pulled back without losing nonvanishing. Dual projections
reverse the inclusion, as required for right-handed conjugate fields.
-/

set_option autoImplicit false

namespace Math.SplitRepresentationProjection

noncomputable section

open Representation

variable {G V W U : Type*} [Group G]
variable [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
variable [AddCommMonoid U] [Module ℂ U]
variable {rho : Representation ℂ G V} {sigma : Representation ℂ G W}
variable {tau : Representation ℂ G U}

def dualMap (f : IntertwiningMap rho sigma) : IntertwiningMap sigma.dual rho.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    apply LinearMap.ext; intro phi
    apply LinearMap.ext; intro x
    change phi (sigma g⁻¹ (f x)) = phi (f (rho g⁻¹ x))
    exact congrArg phi (IntertwiningMap.isIntertwining rho sigma f g⁻¹ x).symm

@[simp] theorem dualMap_apply (f : IntertwiningMap rho sigma) (phi : Module.Dual ℂ W) (x : V) :
    dualMap f phi x = phi (f x) := rfl

def dualEquiv (e : Representation.Equiv rho sigma) :
    Representation.Equiv rho.dual sigma.dual where
  toLinearEquiv := e.toLinearEquiv.symm.dualMap
  isIntertwining' := (dualMap e.symm.toIntertwiningMap).isIntertwining'

def restrictEquiv {K : Type*} [Group K] (e : Representation.Equiv rho sigma)
    (f : K →* G) : Representation.Equiv (rho.comp f) (sigma.comp f) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' k := e.isIntertwining' (f k)

theorem dual_comp {K : Type*} [Group K] (rho : Representation ℂ G V) (f : K →* G) :
    rho.dual.comp f = Representation.dual (rho.comp f) := by
  ext g phi x
  change phi (rho ((f g)⁻¹) x) = phi (rho (f g⁻¹) x)
  rw [map_inv f]

def dualProdEquiv (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    Representation.Equiv (rho.dual.prod sigma.dual) (rho.prod sigma).dual where
  toLinearEquiv := Module.dualProdDualEquivDual ℂ V W
  isIntertwining' g := by
    apply LinearMap.ext; intro phi
    apply LinearMap.ext; intro x
    rfl

def prodEquiv {X : Type*} [AddCommMonoid X] [Module ℂ X]
    {omega : Representation ℂ G X} (e : Representation.Equiv rho sigma)
    (f : Representation.Equiv tau omega) : Representation.Equiv (rho.prod tau) (sigma.prod omega) where
  toLinearEquiv := e.toLinearEquiv.prodCongr f.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext; intro x
    exact Prod.ext (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x.1)
      (IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g x.2)

theorem prodEquiv_apply {X : Type*} [AddCommMonoid X] [Module ℂ X]
    {omega : Representation ℂ G X} (e : Representation.Equiv rho sigma)
    (f : Representation.Equiv tau omega) (x : V × U) :
    prodEquiv e f x = (e x.1, f x.2) := rfl

def bidualEquiv (rho : Representation ℂ G V) [Module.IsReflexive ℂ V] :
    Representation.Equiv rho rho.dual.dual where
  toLinearEquiv := Module.evalEquiv ℂ V
  isIntertwining' g := by
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro phi
    change phi (rho g x) = phi (rho g⁻¹⁻¹ x)
    rw [inv_inv]

structure Split (rho : Representation ℂ G V) (sigma : Representation ℂ G W) where
  project : IntertwiningMap rho sigma
  embed : IntertwiningMap sigma rho
  left_inv : ∀ x, project (embed x) = x

namespace Split

def ofEquiv (e : Representation.Equiv rho sigma) : Split rho sigma where
  project := e.toIntertwiningMap
  embed := e.symm.toIntertwiningMap
  left_inv := e.toLinearEquiv.apply_symm_apply

def trans (S : Split rho sigma) (T : Split sigma tau) : Split rho tau where
  project := T.project.comp S.project
  embed := S.embed.comp T.embed
  left_inv x := by simp only [IntertwiningMap.comp_apply, S.left_inv, T.left_inv]

def fst (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    Split (rho.prod sigma) rho where
  project := IntertwiningMap.fst ℂ rho sigma
  embed := IntertwiningMap.inl ℂ rho sigma
  left_inv _ := rfl

def snd (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    Split (rho.prod sigma) sigma where
  project := IntertwiningMap.snd ℂ rho sigma
  embed := IntertwiningMap.inr ℂ rho sigma
  left_inv _ := rfl

def dual (S : Split rho sigma) : Split rho.dual sigma.dual where
  project := dualMap S.embed
  embed := dualMap S.project
  left_inv phi := by
    apply LinearMap.ext
    intro x
    change phi (S.project (S.embed x)) = phi x
    rw [S.left_inv]

variable {X Y : Type*} [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
variable {pi : Representation ℂ G X} {omega : Representation ℂ G Y}

def tensor (S : Split rho sigma) (T : Split pi omega) :
    Split (rho.tprod pi) (sigma.tprod omega) where
  project := S.project.tensor T.project
  embed := S.embed.tensor T.embed
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul v w => simp [S.left_inv, T.left_inv]
    | add a b ha hb => simp only [map_add, ha, hb]

theorem pullback_nonzero (S : Split rho sigma) (f : W →ₗ[ℂ] ℂ) (hf : f ≠ 0) :
    f.comp S.project.toLinearMap ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun h (S.embed x)
  simpa only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
    S.left_inv, LinearMap.zero_apply] using he

theorem pullback_invariant (S : Split rho sigma) (f : W →ₗ[ℂ] ℂ)
    (hf : ∀ g x, f (sigma g x) = f x) (g : G) (x : V) :
    (f.comp S.project.toLinearMap) (rho g x) = (f.comp S.project.toLinearMap) x := by
  change f (S.project (rho g x)) = f (S.project x)
  rw [IntertwiningMap.isIntertwining _ _ S.project]
  exact hf g _

/-- An exact pullback with its reusable proof interface. Hiding the large
coordinate expression avoids repeatedly expanding chosen field bases. -/
structure PullbackCertificate (S : Split rho sigma) (f : W →ₗ[ℂ] ℂ) where
  form : V →ₗ[ℂ] ℂ
  form_eq : form = f.comp S.project.toLinearMap
  apply_embed : ∀ x, form (S.embed x) = f x
  nonzero_of : f ≠ 0 → form ≠ 0
  invariant_of : (∀ g x, f (sigma g x) = f x) → ∀ g x, form (rho g x) = form x

def certificate (S : Split rho sigma) (f : W →ₗ[ℂ] ℂ) : PullbackCertificate S f :=
  Classical.choice ⟨{
    form := f.comp S.project.toLinearMap
    form_eq := rfl
    apply_embed := fun x => congrArg f (S.left_inv x)
    nonzero_of := S.pullback_nonzero f
    invariant_of := S.pullback_invariant f }⟩

end Split

end

end Math.SplitRepresentationProjection
