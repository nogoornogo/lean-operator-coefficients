import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import TauCeti.RepresentationTheory.Subrepresentation
import Mathlib.Tactic

/-! Equivariant solution of two identical-representation mixing constraints. -/
set_option autoImplicit false
namespace TwoCopyKernel
noncomputable section
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
variable (rho : Representation ℂ G V) (sigma : Representation ℂ G W)

def sector (a b : ℂ) : Subrepresentation (rho.prod (sigma.prod sigma)) where
  toSubmodule := {
    carrier := {x | a • x.1 = 0 ∧ b • x.1 = 0 ∧ a • x.2.1 + b • x.2.2 = 0}
    zero_mem' := by simp
    add_mem' {x} {y} hx hy := by
      change a • (x.1 + y.1) = 0 ∧ b • (x.1 + y.1) = 0 ∧
        a • (x.2.1 + y.2.1) + b • (x.2.2 + y.2.2) = 0
      simp only [smul_add]
      exact ⟨by rw [hx.1, hy.1, add_zero], by rw [hx.2.1, hy.2.1, add_zero], by
        rw [add_add_add_comm, hx.2.2, hy.2.2, add_zero]⟩
    smul_mem' c x hx := by
      change a • (c • x.1) = 0 ∧ b • (c • x.1) = 0 ∧
        a • (c • x.2.1) + b • (c • x.2.2) = 0
      simp only [smul_comm a c, smul_comm b c,
        ← smul_add, hx.1, hx.2.1, hx.2.2, smul_zero, and_self] }
  apply_mem_toSubmodule g x hx := by
    change a • rho g x.1 = 0 ∧ b • rho g x.1 = 0 ∧
      a • sigma g x.2.1 + b • sigma g x.2.2 = 0
    rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add,
      hx.1, hx.2.1, hx.2.2, map_zero, map_zero]
    exact ⟨rfl, rfl, rfl⟩

theorem solve {a b : ℂ} (hb : b ≠ 0) (f g : W) (h : a • f + b • g = 0) :
    g = (-a / b) • f := by
  have he : b • g = -(a • f) := eq_neg_of_add_eq_zero_right h
  calc
    g = b⁻¹ • (b • g) := (inv_smul_smul₀ hb g).symm
    _ = (-a / b) • f := by rw [he]; simp [smul_smul, div_eq_mul_inv, mul_comm]

def ofRight (a b : ℂ) (hb : b ≠ 0) :
    Representation.Equiv (sector rho sigma a b).toRepresentation sigma where
  toLinearEquiv := {
    toFun x := x.val.2.1
    invFun y := ⟨(0, (y, (-a / b) • y)), by
      refine ⟨smul_zero _, smul_zero _, ?_⟩
      rw [smul_smul, ← add_smul]
      have he : a + b * (-a / b) = 0 := by field_simp; ring
      rw [he, zero_smul]⟩
    left_inv x := by
      apply Subtype.ext
      have hz : x.val.1 = 0 := (smul_eq_zero.mp x.property.2.1).resolve_left hb
      exact Prod.ext hz.symm (Prod.ext rfl (solve hb _ _ x.property.2.2).symm)
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def swap (a b : ℂ) : Representation.Equiv
    (sector rho sigma a b).toRepresentation (sector rho sigma b a).toRepresentation where
  toLinearEquiv := {
    toFun x := ⟨(x.val.1, (x.val.2.2, x.val.2.1)),
      ⟨x.property.2.1, x.property.1, by simpa [add_comm] using x.property.2.2⟩⟩
    invFun x := ⟨(x.val.1, (x.val.2.2, x.val.2.1)),
      ⟨x.property.2.1, x.property.1, by simpa [add_comm] using x.property.2.2⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def ofNonzero (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) :
    Representation.Equiv (sector rho sigma a b).toRepresentation sigma := by
  by_cases hb : b = 0
  · exact (swap rho sigma a b).trans (ofRight rho sigma b a (h.resolve_right (not_not.mpr hb)))
  · exact ofRight rho sigma a b hb

def ofZero : Representation.Equiv (sector rho sigma 0 0).toRepresentation
    (rho.prod (sigma.prod sigma)) where
  toLinearEquiv := {
    toFun x := x.val
    invFun x := ⟨x, by simp [sector]⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

end
end TwoCopyKernel
