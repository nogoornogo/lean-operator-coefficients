import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel

/-! A linear evaluation with a specified section splits off its invisible kernel. -/
set_option autoImplicit false
namespace SplitEvaluation
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (E : V →ₗ[K] W) (S : W →ₗ[K] V) (h : ∀ w, E (S w) = w)

def equiv : V ≃ₗ[K] E.ker × W where
  toFun v := (⟨v - S (E v), by simp only [LinearMap.mem_ker, map_sub, h, sub_self]⟩, E v)
  invFun p := p.1.val + S p.2
  left_inv v := sub_add_cancel v _
  right_inv p := by
    have hp : E p.1.val = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add, hp, h, zero_add, add_sub_cancel_right]
    · simp only [map_add, hp, h, zero_add]
  map_add' v w := by
    apply Prod.ext
    · apply Subtype.ext
      change v + w - S (E (v + w)) = (v - S (E v)) + (w - S (E w))
      simp only [map_add]
      abel
    · exact E.map_add v w
  map_smul' c v := by
    apply Prod.ext
    · apply Subtype.ext
      change c • v - S (E (c • v)) = c • (v - S (E v))
      simp only [map_smul, smul_sub]
    · exact E.map_smul c v

include S h in
theorem surjective : Function.Surjective E := fun w => ⟨S w, h w⟩

def equivWithKernel (P : Submodule K V) (hP : E.ker = P) : V ≃ₗ[K] P × W :=
  (equiv E S h).trans ((LinearEquiv.ofEq _ _ hP).prodCongr (LinearEquiv.refl K W))

theorem equivWithKernel_symm_apply (P : Submodule K V) (hP : E.ker = P) (p : P × W) :
    (equivWithKernel E S h P hP).symm p = p.1.val + S p.2 := by
  subst P
  rfl

include S h in
theorem finrank [FiniteDimensional K V] [FiniteDimensional K W] :
    Module.finrank K V = Module.finrank K E.ker + Module.finrank K W := by
  rw [(equiv E S h).finrank_eq, Module.finrank_prod]

end
end SplitEvaluation
