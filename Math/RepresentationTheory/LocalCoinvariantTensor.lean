import Math.RepresentationTheory.LocalCoinvariantHom
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RepresentationTheory.Basic

/-! Local coinvariants commute with tensoring an arbitrary multiplicity module.
The local group acts trivially on the multiplicity factor. -/
namespace Math.LocalCoinvariantTensor
set_option autoImplicit false
noncomputable section
open Representation LocalCoinvariantHom
open scoped TensorProduct
variable {k G L M : Type*} [Field k] [Group G]
  [AddCommGroup L] [Module k L] [AddCommGroup M] [Module k M]
  (a : Representation k G L)

def action : Representation k G (L ⊗[k] M) := a.tprod (trivial k G M)

theorem relation_tmul (g : G) (x : L) (y : M) :
    relation (action (M := M) a) (g,x ⊗ₜ[k] y) = relation a (g,x) ⊗ₜ[k] y := by
  simp [relation, action, Representation.tprod_apply, TensorProduct.sub_tmul]

theorem tmul_mem (x : L) (hx : x ∈ relations a) (y : M) :
    x ⊗ₜ[k] y ∈ relations (action (M := M) a) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g,v⟩,rfl⟩ := hx
    rw [← relation_tmul]
    exact Submodule.subset_span ⟨_,rfl⟩
  | zero => simp
  | add x z hx hz ihx ihz =>
    rw [TensorProduct.add_tmul]
    exact Submodule.add_mem _ ihx ihz
  | smul c x hx ih =>
    rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c ih

theorem relations_eq_range : relations (action (M := M) a) =
    LinearMap.range (TensorProduct.map (relations a).subtype (LinearMap.id : M →ₗ[k] M)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,u⟩,rfl⟩
    induction u using TensorProduct.inductionOn with
    | tmul x y =>
      rw [relation_tmul]
      exact ⟨⟨relation a (g,x), Submodule.subset_span ⟨_,rfl⟩⟩ ⊗ₜ[k] y,rfl⟩
    | add u v hu hv =>
      have he : relation (action (M := M) a) (g,u+v) =
          relation (action (M := M) a) (g,u) + relation (action (M := M) a) (g,v) := by
        simp [relation, map_add, sub_add_sub_comm]
      rw [he]
      exact Submodule.add_mem _ hu hv
  · rintro _ ⟨z,rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact tmul_mem a x.val x.property y
    | add u v hu hv =>
      rw [map_add]
      exact Submodule.add_mem _ hu hv

def equiv : (L ⧸ relations a) ⊗[k] M ≃ₗ[k]
    (L ⊗[k] M) ⧸ relations (action (M := M) a) :=
  (TensorProduct.quotientTensorEquiv M (relations a)).trans
    (Submodule.Quotient.equiv _ _ (LinearEquiv.refl k _) (by
      simpa using (relations_eq_range (M := M) a).symm))

@[simp] theorem equiv_tmul_mk (x : L) (y : M) :
    equiv a ((relations a).mkQ x ⊗ₜ[k] y) =
      (relations (action (M := M) a)).mkQ (x ⊗ₜ[k] y) := rfl

section Residual
variable {H : Type*} [Group H] (b : Representation k H M)

def residual : Representation k H (L ⊗[k] M) := (trivial k H L).tprod b

theorem commutes (g : G) (h : H) (u : L ⊗[k] M) :
    action a g (residual b h u) = residual b h (action a g u) := by
  have he : (action (M := M) a g).comp (residual (L := L) b h) =
      (residual (L := L) b h).comp (action a g) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact LinearMap.congr_fun he u

def residualEquiv : Representation.Equiv
    ((trivial k H (L ⧸ relations a)).tprod b)
    (LocalCoinvariantHom.quotient (action a) (residual b) (commutes a b)) where
  toLinearEquiv := equiv a
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro x y
    obtain ⟨v,rfl⟩ := (relations a).mkQ_surjective x
    rfl

end Residual

end
end Math.LocalCoinvariantTensor
