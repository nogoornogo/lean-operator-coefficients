import Math.RepresentationTheory.FourSlotTripleSector
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Species-preserving field identifications preserve the intrinsic (3,1) sector. -/
namespace Math.FourSlotTripleTransport
set_option autoImplicit false
noncomputable section
open Representation FourSlotTripleSector SplitRepresentationProjection
variable {H A B A' B' : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup A'] [Module ℂ A'] [AddCommGroup B'] [Module ℂ B']
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {a' : Representation ℂ H A'} {b' : Representation ℂ H B'}
  (ea : Representation.Equiv a a') (eb : Representation.Equiv b b')

def pull (f : Coefficient a' b') : Coefficient a b :=
  f.comp ((prodEquiv ea eb).exteriorPower 4).toIntertwiningMap

theorem pull_mem (f : sector a' b') : pull ea eb f.val ∈ sector a b := by
  intro labels hl v
  change f.val (((prodEquiv ea eb).exteriorPower 4)
    (exteriorPower.ιMulti ℂ 4 (fun i => project (labels i) (v i)))) = 0
  rw [Representation.Equiv.exteriorPower_apply_ιMulti]
  have he : (fun i => prodEquiv ea eb (project (labels i) (v i))) =
      (fun i => project (labels i) (ea (v i).1, eb (v i).2)) := by
    funext i
    change (ea (project (labels i) (v i)).1, eb (project (labels i) (v i)).2) = _
    by_cases hi : labels i = 0 <;> simp [project, hi]
  simp only [Function.comp_def]
  rw [he]
  exact f.property labels hl (fun i => (ea (v i).1, eb (v i).2))

def pullLinear : sector a' b' →ₗ[ℂ] sector a b where
  toFun f := ⟨pull ea eb f.val, pull_mem ea eb f⟩
  map_add' f g := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

theorem pull_symm (f : Coefficient a b) : pull ea eb (pull ea.symm eb.symm f) = f := by
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  ext v
  change f (((prodEquiv ea.symm eb.symm).exteriorPower 4)
    (((prodEquiv ea eb).exteriorPower 4) (exteriorPower.ιMulti ℂ 4 v))) = _
  rw [Representation.Equiv.exteriorPower_apply_ιMulti, Representation.Equiv.exteriorPower_apply_ιMulti]
  apply congrArg f
  apply congrArg (exteriorPower.ιMulti ℂ 4)
  funext i
  change (ea.symm (ea (v i).1), eb.symm (eb (v i).2)) = v i
  simp

def equiv : sector a' b' ≃ₗ[ℂ] sector a b where
  toFun := pullLinear ea eb
  invFun := pullLinear ea.symm eb.symm
  left_inv f := by apply Subtype.ext; exact pull_symm ea.symm eb.symm f.val
  right_inv f := by apply Subtype.ext; exact pull_symm ea eb f.val
  map_add' := (pullLinear ea eb).map_add
  map_smul' := (pullLinear ea eb).map_smul

end
end Math.FourSlotTripleTransport
