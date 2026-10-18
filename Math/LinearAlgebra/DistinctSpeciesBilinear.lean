import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The mixed two-fermion sector has no symmetry condition between distinct
species. Bosonic slots may be kept in the value module. -/
namespace Math.DistinctSpeciesBilinear
set_option autoImplicit false
variable {L E N : Type*} [AddCommGroup L] [Module ℂ L]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup N] [Module ℂ N]

def extend (f : L →ₗ[ℂ] E →ₗ[ℂ] N) : (L × E) →ₗ[ℂ] (L × E) →ₗ[ℂ] N :=
  LinearMap.mk₂ ℂ (fun x y => f x.1 y.2 - f y.1 x.2)
    (by intro x x' y; simp [map_add, LinearMap.add_apply]; abel)
    (by intro z x y; simp [map_smul, LinearMap.smul_apply, smul_sub])
    (by intro x y y'; simp [map_add, LinearMap.add_apply]; abel)
    (by intro z x y; simp [map_smul, LinearMap.smul_apply, smul_sub])

@[simp] theorem extend_apply (f : L →ₗ[ℂ] E →ₗ[ℂ] N) (x y : L × E) :
    extend f x y = f x.1 y.2 - f y.1 x.2 := rfl

@[simp] theorem extend_diagonal (f : L →ₗ[ℂ] E →ₗ[ℂ] N) (x : L × E) :
    extend f x x = 0 := sub_self _

@[simp] theorem extend_restrict (f : L →ₗ[ℂ] E →ₗ[ℂ] N) (l : L) (e : E) :
    extend f (l,0) (0,e) = f l e := by simp

theorem extend_injective : Function.Injective (extend (L := L) (E := E) (N := N)) := by
  intro f g h
  ext l e
  simpa only [extend_restrict] using congrArg (fun k => k (l,0) (0,e)) h

theorem reconstruct (g : (L × E) →ₗ[ℂ] (L × E) →ₗ[ℂ] N)
    (ha : ∀ x, g x x = 0)
    (hL : ∀ l l', g (l,0) (l',0) = 0)
    (hE : ∀ e e', g (0,e) (0,e') = 0) (x y : L × E) :
    g x y = g (x.1,0) (0,y.2) - g (y.1,0) (0,x.2) := by
  have skew (u v : L × E) : g v u = -g u v := by
    have h := ha (u+v)
    simp only [map_add, LinearMap.add_apply, ha, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hx : x = (x.1,0) + (0,x.2) := by ext <;> simp
  have hy : y = (y.1,0) + (0,y.2) := by ext <;> simp
  conv_lhs => rw [hx,hy]
  simp only [map_add, LinearMap.add_apply, hL, hE, zero_add, add_zero]
  rw [skew]
  abel

end Math.DistinctSpeciesBilinear
