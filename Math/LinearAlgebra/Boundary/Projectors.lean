import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Module

/-! Algebraic boundary amplitudes for complementary chiral projectors.
This module makes no assertion about differential equations or mode profiles. -/
namespace Math.BoundaryProjectors
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure Pair where
  uv : V →ₗ[K] V
  ir : V →ₗ[K] V
  uv_idem : uv.comp uv = uv
  ir_idem : ir.comp ir = ir
  commute : uv.comp ir = ir.comp uv

namespace Pair
variable (P : Pair (K := K) (V := V))

def selected : Submodule K V := LinearMap.ker (P.uv - LinearMap.id) ⊓
  LinearMap.ker (P.ir - LinearMap.id)

@[simp] theorem mem_selected (v : V) :
    v ∈ P.selected ↔ P.uv v = v ∧ P.ir v = v := by
  simp [selected, sub_eq_zero]

def opposite : Pair (K := K) (V := V) where
  uv := LinearMap.id - P.uv
  ir := LinearMap.id - P.ir
  uv_idem := by ext v; have h := LinearMap.congr_fun P.uv_idem v
                change P.uv (P.uv v) = P.uv v at h
                simp [h]
  ir_idem := by ext v; have h := LinearMap.congr_fun P.ir_idem v
                change P.ir (P.ir v) = P.ir v at h
                simp [h]
  commute := by ext v; have h := LinearMap.congr_fun P.commute v
                change P.uv (P.ir v) = P.ir (P.uv v) at h
                simp [h]; module

@[simp] theorem mem_opposite (v : V) :
    v ∈ P.opposite.selected ↔ P.uv v = 0 ∧ P.ir v = 0 := by
  simp [opposite, sub_eq_self]

theorem joint_mem (v : V) : P.uv (P.ir v) ∈ P.selected := by
  rw [mem_selected]
  constructor
  · exact LinearMap.congr_fun P.uv_idem (P.ir v)
  · have hc := LinearMap.congr_fun P.commute (P.ir v)
    have hi := LinearMap.congr_fun P.ir_idem v
    change P.uv (P.ir (P.ir v)) = P.ir (P.uv (P.ir v)) at hc
    change P.ir (P.ir v) = P.ir v at hi
    rw [← hc, hi]

theorem range_joint : LinearMap.range (P.uv.comp P.ir) = P.selected := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩; exact P.joint_mem w
  · intro hv
    obtain ⟨hu, hi⟩ := (P.mem_selected v).mp hv
    exact ⟨v, by simp [hi, hu]⟩

theorem preserved (a : V →ₗ[K] V)
    (hu : P.uv.comp a = a.comp P.uv) (hi : P.ir.comp a = a.comp P.ir)
    {v : V} (hv : v ∈ P.selected) : a v ∈ P.selected := by
  obtain ⟨huv, hiv⟩ := (P.mem_selected v).mp hv
  rw [mem_selected]
  exact ⟨(LinearMap.congr_fun hu v).trans (congrArg a huv),
    (LinearMap.congr_fun hi v).trans (congrArg a hiv)⟩

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A proved retraction and exact selected-image criterion give an equivalence. -/
def equivalence (e : W →ₗ[K] V) (p : V →ₗ[K] W) (hp : ∀ w, p (e w) = w)
    (he : ∀ v, v ∈ P.selected ↔ e (p v) = v) : W ≃ₗ[K] P.selected where
  toFun w := ⟨e w, (he _).mpr (by rw [hp])⟩
  invFun v := p v.val
  left_inv := hp
  right_inv v := Subtype.ext ((he v.val).mp v.property)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

end Pair
end Math.BoundaryProjectors
