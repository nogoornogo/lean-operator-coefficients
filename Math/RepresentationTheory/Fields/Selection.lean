import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining
import Math.LinearAlgebra.Boundary.Projectors

/-! Stable field selection and constructive exact dictionaries. No decomposition,
unitarity, abelian-group or global equivariant-retraction hypothesis is used. -/
namespace Math.FieldSelection
set_option autoImplicit false
noncomputable section
open Representation
variable {k G H U V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  {rho : Representation k G U} {tau : Representation k G V}

theorem equiv_comp_symm (e : Equiv rho tau) :
    e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
  LinearMap.ext e.toLinearEquiv.apply_symm_apply

theorem equiv_symm_comp (e : Equiv rho tau) :
    e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id :=
  LinearMap.ext e.toLinearEquiv.symm_apply_apply

def inclusion (S : Subrepresentation rho) : IntertwiningMap S.toRepresentation rho where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

def kernel (f : IntertwiningMap rho tau) : Subrepresentation rho where
  toSubmodule := f.toLinearMap.ker
  apply_mem_toSubmodule g u hu := by
    change f (rho g u) = 0
    rw [IntertwiningMap.isIntertwining, show f u = 0 from hu, map_zero]

/-- A concrete subspace whose elements reconstruct through an equivariant
inclusion is stable. Ambient extraction need not intertwine. -/
def realized (e : IntertwiningMap tau rho) (p : U →ₗ[k] V)
    (S : Submodule k U) (he : ∀ v, e v ∈ S)
    (hs : ∀ u, u ∈ S → e (p u) = u) : Subrepresentation rho where
  toSubmodule := S
  apply_mem_toSubmodule g u hu := by
    rw [← hs u hu, ← IntertwiningMap.isIntertwining tau rho e g (p u)]
    exact he _

/-- Common constraints do not require the constraint maps to commute. -/
def fixed {J : Type*} (rho : Representation k G U) (p : J → U →ₗ[k] U)
    (hp : ∀ j g u, p j (rho g u) = rho g (p j u)) : Subrepresentation rho where
  toSubmodule := ⨅ j, (p j - LinearMap.id).ker
  apply_mem_toSubmodule g u hu := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hu ⊢
    intro j
    rw [hp, hu]

@[simp] theorem mem_fixed {J : Type*} (p : J → U →ₗ[k] U)
    (hp : ∀ j g u, p j (rho g u) = rho g (p j u)) (u : U) :
    u ∈ fixed rho p hp ↔ ∀ j, p j u = u := by
  change u ∈ (⨅ j, (p j - LinearMap.id).ker : Submodule k U) ↔ _
  simp [sub_eq_zero]

def boundary (rho : Representation k G U) (P : BoundaryProjectors.Pair (K := k) (V := U))
    (hu : ∀ g, P.uv.comp (rho g) = (rho g).comp P.uv)
    (hi : ∀ g, P.ir.comp (rho g) = (rho g).comp P.ir) : Subrepresentation rho where
  toSubmodule := P.selected
  apply_mem_toSubmodule g _ hv := P.preserved (rho g) (hu g) (hi g) hv

def restrictGroup (S : Subrepresentation rho) (j : H →* G) :
    Subrepresentation (rho.comp j) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule h := S.apply_mem_toSubmodule (j h)

def reexpress (S : Subrepresentation rho) (e : Equiv rho tau) : Subrepresentation tau where
  toSubmodule := S.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule g _ hv := by
    obtain ⟨u,hu,rfl⟩ := hv
    exact ⟨rho g u, S.apply_mem_toSubmodule g hu,
      IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g u⟩

def reexpressEquiv (S : Subrepresentation rho) (e : Equiv rho tau) :
    Equiv S.toRepresentation (reexpress S e).toRepresentation :=
  .mk
    { toFun := fun u => ⟨e u, ⟨u,u.property,rfl⟩⟩
      invFun := fun v => ⟨e.symm v, by
        obtain ⟨u,hu,he⟩ := v.property
        rw [← he]
        change e.symm (e u) ∈ S.toSubmodule
        exact (e.toLinearEquiv.symm_apply_apply u).symm ▸ hu⟩
      left_inv := fun u => Subtype.ext (e.toLinearEquiv.symm_apply_apply u)
      right_inv := fun v => Subtype.ext (e.toLinearEquiv.apply_symm_apply v)
      map_add' := fun _ _ => Subtype.ext (map_add e _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul e _ _) }
    (by intro g; ext u; exact IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g u)

variable (S : Subrepresentation rho)

/-- Ambient inclusion/extraction construct both inverses. Extraction need only
be linear on the ambient space; its selected equivariance is derived. -/
def ofMaps (e : IntertwiningMap tau rho) (p : U →ₗ[k] V)
    (he : ∀ v, e v ∈ S) (hp : ∀ v, p (e v) = v)
    (hs : ∀ u, u ∈ S → e (p u) = u) : Equiv tau S.toRepresentation :=
  .mk
    { toFun := fun v => ⟨e v, he v⟩
      invFun := fun u => p u
      left_inv := hp
      right_inv := fun u => Subtype.ext (hs u u.property)
      map_add' := fun _ _ => Subtype.ext (map_add e _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul e _ _) }
    (by intro g; ext v; exact IntertwiningMap.isIntertwining _ _ e g v)

@[simp] theorem ofMaps_apply (e : IntertwiningMap tau rho) (p : U →ₗ[k] V)
    (he : ∀ v, e v ∈ S) (hp : ∀ v, p (e v) = v)
    (hs : ∀ u, u ∈ S → e (p u) = u) (v : V) :
    ((ofMaps S e p he hp hs v : S.toSubmodule) : U) = e v := rfl

theorem extraction_covariant (e : IntertwiningMap tau rho) (p : U →ₗ[k] V)
    (he : ∀ v, e v ∈ S) (hp : ∀ v, p (e v) = v)
    (hs : ∀ u, u ∈ S → e (p u) = u) (g : G) (u : S.toSubmodule) :
    p (rho g u) = tau g (p u) :=
  IntertwiningMap.isIntertwining _ _ (ofMaps S e p he hp hs).symm.toIntertwiningMap g u

/-- Exactness is two-sided invertibility on the selected space itself.
An ambient projector is not asserted to exist canonically. -/
theorem exact_iff (e : IntertwiningMap tau S.toRepresentation) :
    Function.Bijective e ↔ ∃ p : S.toSubmodule →ₗ[k] V,
      (∀ v, p (e v) = v) ∧ (∀ u, e (p u) = u) := by
  constructor
  · intro h
    let q := LinearEquiv.ofBijective e.toLinearMap h
    exact ⟨q.symm.toLinearMap, q.symm_apply_apply, q.apply_symm_apply⟩
  · rintro ⟨p,hp,he⟩
    exact ⟨Function.HasLeftInverse.injective ⟨p,hp⟩,
      Function.HasRightInverse.surjective ⟨p,he⟩⟩

end
end Math.FieldSelection
