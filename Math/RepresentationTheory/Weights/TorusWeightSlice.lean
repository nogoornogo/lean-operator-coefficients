import Math.RepresentationTheory.Tensors.ExternalInvariantTensor
import Math.RepresentationTheory.Exterior.ExteriorWeightSupport
import TauCeti.RepresentationTheory.Subrepresentation

/-! Actual circle-weight subrepresentations retaining an independent
commuting action. No inner product, character or multiplicity is needed. -/
namespace Math.TorusWeightSlice
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
variable {G K V W : Type*} [Group G] [Group K]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (rho : Representation ℂ (G × K) V) (t : Circle →* G)

def residual := rho.comp (MonoidHom.inr G K)

def weight (n : ℤ) : Subrepresentation (residual rho) where
  toSubmodule :=
    { carrier := {v | ∀ z : Circle, rho (t z,1) v=(z : ℂ)^n • v}
      zero_mem' := by intro z; simp
      add_mem' := by intro v w hv hw z; rw [map_add, hv z, hw z, smul_add]
      smul_mem' := by intro c v hv z; rw [map_smul, hv z, smul_comm] }
  apply_mem_toSubmodule k {v} hv := by
    intro z
    change rho (t z,1) (rho (1,k) v)=(z : ℂ)^n • rho (1,k) v
    rw [← Module.End.mul_apply, ← map_mul]
    have he : (t z, (1 : K))*((1 : G), k)=((1 : G), k)*(t z,1) := by simp
    rw [he, map_mul, Module.End.mul_apply, hv z, map_smul]

abbrev Space (n : ℤ) := (weight rho t n).toSubmodule
abbrev action (n : ℤ) := (weight rho t n).toRepresentation

@[simp] theorem mem_space (n : ℤ) (v : V) :
    v ∈ Space rho t n ↔ ∀ z : Circle, rho (t z,1) v=(z : ℂ)^n • v := Iff.rfl

/-- Change an equal weight label by the identity on the actual vectors.
Keeping the carrier map explicit avoids transporting a whole representation
equivalence through an equality recursor. -/
def castWeight {n m : ℤ} (h : n=m) : Representation.Equiv (action rho t n) (action rho t m) where
  toLinearEquiv :=
    { toFun x := ⟨x.val, by intro z; rw [← h]; exact x.property z⟩
      invFun x := ⟨x.val, by intro z; rw [h]; exact x.property z⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def transport {sigma : Representation ℂ (G × K) W}
    (e : Representation.Equiv rho sigma) (n : ℤ) :
    Representation.Equiv (action rho t n) (action sigma t n) where
  toLinearEquiv :=
    { toFun v := ⟨e v.val, by
        intro z
        exact (((e.isIntertwining _ _ (t z,1) v.val).symm).trans
          (congrArg e (v.property z))).trans (map_smul e _ _)⟩
      invFun v := ⟨e.symm v.val, by
        intro z
        exact (((e.symm.isIntertwining _ _ (t z,1) v.val).symm).trans
          (congrArg e.symm (v.property z))).trans (map_smul e.symm _ _)⟩
      left_inv v := by apply Subtype.ext; exact e.symm_apply_apply v.val
      right_inv v := by apply Subtype.ext; exact e.apply_symm_apply v.val
      map_add' v w := by apply Subtype.ext; exact map_add e v.val w.val
      map_smul' c v := by apply Subtype.ext; exact map_smul e c v.val }
  isIntertwining' k := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact e.isIntertwining _ _ (1,k) v.val

/-- Distinct integral circle characters remain distinct over the full
circle. This detects weights without selecting numerical sample points. -/
theorem exponent_eq {a b : ℤ} (h : ∀ z : Circle, (z : ℂ)^a=(z : ℂ)^b) : a=b := by
  apply sub_eq_zero.mp
  apply ExteriorWeightSupport.circle_weight_zero (a-b)
  intro z
  rw [zpow_sub₀ z.coe_ne_zero, h z, div_self (zpow_ne_zero _ z.coe_ne_zero)]

theorem eigen_zero_of_ne {U : Type*} [AddCommGroup U] [Module ℂ U]
    {a b : ℤ} (h : a≠b) (x : U)
    (hx : ∀ z : Circle, (z : ℂ)^a • x=(z : ℂ)^b • x) : x=0 := by
  by_contra hn
  exact h (exponent_eq (fun z => (smul_left_injective ℂ hn) (hx z)))

end
end Math.TorusWeightSlice
