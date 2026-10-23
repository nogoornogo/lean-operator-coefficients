import Math.RepresentationTheory.Tensors.ExternalInvariantTensor
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Basis coordinates of invariant functionals, retaining all action equations. -/
namespace Math.InvariantFunctionalCoordinates
set_option autoImplicit false
noncomputable section
open Representation
variable {H V I : Type*} [Group H] [AddCommMonoid V] [Module ℂ V]
  (r : Representation ℂ H V) (b : Module.Basis I ℂ V)

def space : Submodule ℂ (I → ℂ) where
  carrier := {c | ∀ g, (b.constr ℂ c).comp (r g) = b.constr ℂ c}
  zero_mem' := by simp
  add_mem' := by intro c d hc hd g; simp only [map_add, LinearMap.add_comp]; rw [hc,hd]
  smul_mem' := by intro z c hc g; simp only [map_smul, LinearMap.smul_comp]; rw [hc]

def equiv : IntertwiningMap r (Representation.trivial ℂ H ℂ) ≃ₗ[ℂ] space r b where
  toFun f := ⟨(b.constr ℂ).symm f.toLinearMap, by
    intro g
    simp only [LinearEquiv.apply_symm_apply]
    ext v
    exact IntertwiningMap.isIntertwining _ _ f g v⟩
  invFun c := ⟨b.constr ℂ c.val, by
    intro g
    change (b.constr ℂ c.val).comp (r g) = b.constr ℂ c.val
    exact c.property g⟩
  left_inv f := by apply IntertwiningMap.ext; exact (b.constr ℂ).apply_symm_apply f.toLinearMap
  right_inv c := by apply Subtype.ext; exact (b.constr ℂ).symm_apply_apply c.val
  map_add' f g := by apply Subtype.ext; exact (b.constr ℂ).symm.map_add _ _
  map_smul' z f := by apply Subtype.ext; exact (b.constr ℂ).symm.map_smul z _

@[simp] theorem extract_apply (f : IntertwiningMap r (Representation.trivial ℂ H ℂ))
    (i : I) : (equiv r b f).val i = f (b i) := b.constr_symm_apply ℂ _ i

def unrestrictedEquiv (hr : ∀ g, r g = 1) :
    IntertwiningMap r (Representation.trivial ℂ H ℂ) ≃ₗ[ℂ] (I → ℂ) where
  toFun f := (b.constr ℂ).symm f.toLinearMap
  invFun c := ⟨b.constr ℂ c, by intro g; rw [hr]; rfl⟩
  left_inv f := by apply IntertwiningMap.ext; exact (b.constr ℂ).apply_symm_apply _
  right_inv c := (b.constr ℂ).symm_apply_apply c
  map_add' f g := (b.constr ℂ).symm.map_add _ _
  map_smul' z f := (b.constr ℂ).symm.map_smul z _

def trivialEquiv : IntertwiningMap (Representation.trivial ℂ H V)
    (Representation.trivial ℂ H ℂ) ≃ₗ[ℂ] (I → ℂ) where
  toFun f := (b.constr ℂ).symm f.toLinearMap
  invFun c := ⟨b.constr ℂ c, by intro g; rfl⟩
  left_inv f := by apply IntertwiningMap.ext; exact (b.constr ℂ).apply_symm_apply _
  right_inv c := (b.constr ℂ).symm_apply_apply c
  map_add' f g := (b.constr ℂ).symm.map_add _ _
  map_smul' z f := (b.constr ℂ).symm.map_smul z _

include b in
theorem finrank [Fintype I] :
    Module.finrank ℂ (IntertwiningMap (Representation.trivial ℂ H V)
      (Representation.trivial ℂ H ℂ)) = Fintype.card I := by
  rw [(trivialEquiv (H := H) b).finrank_eq]
  simp
end
end Math.InvariantFunctionalCoordinates
