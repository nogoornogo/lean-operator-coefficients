import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Tactic

/-! Complete graph coordinates for a neutral block mass and actual coefficient
restriction. No symmetry, kinetic form or nonzero generation is inferred. -/
namespace Math.NeutralKernelGraph
set_option autoImplicit false
noncomputable section
variable {k A B C : Type*} [Field k] [AddCommGroup A] [Module k A]
  [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]

abbrev Full (A B C : Type*) := A × B × C

def graph (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) : A →ₗ[k] Full A B C where
  toFun a := (a,0,-M.symm (D a))
  map_add' a b := by simp [add_comm]
  map_smul' c a := by simp

def mass (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) (E : B →ₗ[k] A) (N : B →ₗ[k] C) :
    Full A B C →ₗ[k] Full A B C where
  toFun x := (E x.2.1,D x.1+M x.2.2,N x.2.1)
  map_add' a b := by simp; abel
  map_smul' c a := by simp [smul_add]

theorem graph_kernel (D : A →ₗ[k] B) (M : C ≃ₗ[k] B)
    (E : B →ₗ[k] A) (N : B →ₗ[k] C) (a : A) : mass D M E N (graph D M a) = 0 := by
  simp [mass,graph]

theorem kernel_iff (D : A →ₗ[k] B) (M : C ≃ₗ[k] B)
    (E : B →ₗ[k] A) (N : B →ₗ[k] C) (hN : Function.Injective N)
    (x : Full A B C) : mass D M E N x = 0 ↔ x = graph D M x.1 := by
  constructor
  · intro h
    have hb := congrArg (fun y : Full A B C => y.2.2) h
    have hm := congrArg (fun y : Full A B C => y.2.1) h
    have hz : x.2.1 = 0 := hN (by simpa [mass] using hb)
    have hc : x.2.2 = -M.symm (D x.1) := by
      apply M.injective
      have hm' : D x.1+M x.2.2=0 := hm
      simpa using (eq_neg_of_add_eq_zero_right hm')
    exact Prod.ext rfl (Prod.ext hz hc)
  · intro h
    rw [h]
    exact graph_kernel D M E N _

theorem graph_injective (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) :
    Function.Injective (graph D M) := by
  intro a b h
  exact congrArg Prod.fst h

variable {n : ℕ}
def restrict (f : (Full A B C) [⋀^Fin n]→ₗ[k] k)
    (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) := f.compLinearMap (graph D M)

theorem restrict_apply (f : (Full A B C) [⋀^Fin n]→ₗ[k] k)
    (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) (a : Fin n → A) :
    restrict f D M a = f (graph D M ∘ a) := rfl

theorem restrict_nonzero_iff (f : (Full A B C) [⋀^Fin n]→ₗ[k] k)
    (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) :
    restrict f D M ≠ 0 ↔ ∃ a, f (graph D M ∘ a) ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    ext a
    exact hn a
  · rintro ⟨a,ha⟩ hz
    exact ha (DFunLike.congr_fun hz a)

theorem restrict_zero_iff_on_kernel (f : (Full A B C) [⋀^Fin n]→ₗ[k] k)
    (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) (E : B →ₗ[k] A) (N : B →ₗ[k] C)
    (hN : Function.Injective N) :
    restrict f D M = 0 ↔ ∀ x : Fin n → Full A B C,
      (∀ i, mass D M E N (x i) = 0) → f x = 0 := by
  constructor
  · intro hz x hx
    have he : graph D M ∘ (fun i => (x i).1) = x := by
      funext i
      exact ((kernel_iff D M E N hN (x i)).mp (hx i)).symm
    have hv := DFunLike.congr_fun hz (fun i => (x i).1)
    simpa only [restrict_apply, he, AlternatingMap.zero_apply] using hv
  · intro hx
    ext a
    exact hx (graph D M ∘ a) (fun i => graph_kernel D M E N (a i))

theorem restrict_change_coordinates (f : (Full A B C) [⋀^Fin n]→ₗ[k] k)
    (D : A →ₗ[k] B) (M : C ≃ₗ[k] B) (e : A ≃ₗ[k] A) :
    (restrict f D M).compLinearMap e.toLinearMap ≠ 0 ↔ restrict f D M ≠ 0 := by
  constructor
  · intro h hz
    rw [hz] at h
    exact h (by ext a; rfl)
  · intro h hz
    apply h
    ext a
    have hv := DFunLike.congr_fun hz (fun i => e.symm (a i))
    simpa using hv

end
end Math.NeutralKernelGraph
