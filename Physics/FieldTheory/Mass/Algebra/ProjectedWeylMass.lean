import Physics.FieldTheory.Mass.Algebra.SplitWeylMass

/-! Define the split mass from its heavy projections, before imposing a group action. -/
namespace Physics.ProjectedWeylMass
set_option autoImplicit false
noncomputable section
open InvariantWeylMass

variable {V L F : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup L] [Module ℂ L] [AddCommGroup F] [Module ℂ F]

abbrev Fields := (L × F) × Module.Dual ℂ F

def projection (E : V ≃ₗ[ℂ] Fields (L := L) (F := F)) :
    V →ₗ[ℂ] F × Module.Dual ℂ F :=
  (((LinearMap.snd ℂ L F).comp (LinearMap.fst ℂ (L × F) (Module.Dual ℂ F))).prod
    (LinearMap.snd ℂ (L × F) (Module.Dual ℂ F))).comp E.toLinearMap

@[simp] theorem projection_apply (E : V ≃ₗ[ℂ] Fields (L := L) (F := F)) (x : V) :
    projection E x = ((E x).1.2, (E x).2) := rfl

def form (E : V ≃ₗ[ℂ] Fields (L := L) (F := F)) : LinearMap.BilinForm ℂ V :=
  (DiracWeylConvention.massBilinear (LinearMap.id : F →ₗ[ℂ] F)).compl₁₂
    (projection E) (projection E)

theorem form_apply (E : V ≃ₗ[ℂ] Fields (L := L) (F := F)) (x y : V) :
    form E x y = (E y).2 (E x).1.2 + (E x).2 (E y).1.2 := rfl

variable {G : Type*} [Group G]

theorem form_eq_split (E : V ≃ₗ[ℂ] Fields (L := L) (F := F))
    (rhoL : Representation ℂ G L) (rhoF : Representation ℂ G F) :
    form E = (SplitWeylMass.mass rhoL rhoF).form.compl₁₂ E.toLinearMap E.toLinearMap := rfl

/-- The projection criterion is proved for an arbitrary mass with this form. -/
theorem mem_radical_of_projection {rho : Representation ℂ G V}
    (M : SymmetricMass rho) (E : V ≃ₗ[ℂ] Fields (L := L) (F := F))
    (h : M.form = form E) (x : V) (hx : projection E x = 0) :
    x ∈ M.radical.toSubmodule := by
  rw [SymmetricMass.mem_radical]
  intro y
  have hf : (E x).1.2 = 0 := congrArg Prod.fst hx
  have hp : (E x).2 = 0 := congrArg Prod.snd hx
  rw [h, form_apply, hf, hp]
  simp

end
end Physics.ProjectedWeylMass
