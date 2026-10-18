import Math.LinearAlgebra.ExteriorFourthDoubletCross
import Math.LinearAlgebra.ExteriorFourthDimensions

/-! Complete quartic doublet Cauchy decomposition. Independence is proved
by actual contractions; exhaustion uses only the symbolic dimension identity. -/
namespace Math.ExteriorFourthDoubletCauchy
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open ExteriorFourthDoublet ExteriorFourthDoublet22 ExteriorFourthDoubletCross
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
@[reducible] local instance : AddCommGroup (ExteriorFourthKernels.Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
abbrev Domain := ExteriorFourthDimensions.Candidate (A := A) (B := B)
@[reducible] local instance : AddCommGroup (Domain (A := A)) := inferInstance

def combine : Domain (A := A) →ₗ[ℂ] Total (A := A) :=
  (ExteriorSymmetricColumn.column 4).comp (LinearMap.fst ℂ _ _)+
    insert211.comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))+
    insertK22.comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))

theorem combine_apply (x : Domain (A := A)) : combine x=
    ExteriorSymmetricColumn.column 4 x.1+insert211 x.2.1+insertK22 x.2.2 := rfl

theorem combine_injective : Function.Injective (combine (A := A)) := by
  intro x y h
  have hm := congrArg retract211 h
  simp only [combine_apply, map_add, retract211_column, retract211_insert211,
    retract211_insertK22, zero_add, add_zero] at hm
  have hl := congrArg retractK22 h
  simp only [combine_apply, map_add, retractK22_column, retractK22_insert211,
    retractK22_insertK22, zero_add] at hl
  have ht : ExteriorSymmetricColumn.column 4 x.1=ExteriorSymmetricColumn.column 4 y.1 := by
    rw [combine_apply, combine_apply, hm, hl] at h
    exact add_right_cancel (add_right_cancel h)
  exact Prod.ext (ExteriorFourthColumn.column_injective ht) (Prod.ext hm hl)

theorem combine_surjective [FiniteDimensional ℂ A] :
    Function.Surjective (combine (A := A)) :=
  ExteriorFourthDimensions.surjective_of_injective
    (by simp [B, WeakDoubletScalars.Doublet]) combine combine_injective

/-- All three actual branches exhaust the quartic exterior power. -/
def equivalence [FiniteDimensional ℂ A] : Domain (A := A) ≃ₗ[ℂ] Total (A := A) :=
  LinearEquiv.ofBijective combine ⟨combine_injective, combine_surjective⟩

@[reducible] local instance : AddCommGroup (ExteriorFourthColumn.Column (A := A) (B := B)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup
    (ExteriorFourthKernels.K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) := inferInstance
@[reducible] local instance : AddCommGroup
    (ExteriorFourthColumn.Remainder (A := A) (B := B)) := inferInstance

abbrev Tail := (ExteriorFourthKernels.K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) ×
  ExteriorFourthKernels.K22 (A := A)
@[reducible] local instance : AddCommGroup (Tail (A := A)) := inferInstance

theorem project_column (x : ExteriorFourthColumn.Column (A := A) (B := B)) :
    ExteriorFourthColumn.project (ExteriorSymmetricColumn.column 4 x)=0 :=
  SectionKernel.project_section (ExteriorFourthColumn.retract (A := A) (B := B))
    (ExteriorSymmetricColumn.column 4) ExteriorFourthColumn.retract_column x

theorem project_kernel (x : ExteriorFourthColumn.Remainder (A := A) (B := B)) :
    ExteriorFourthColumn.project x.val=x :=
  SectionKernel.project_kernel (ExteriorFourthColumn.retract (A := A) (B := B))
    (ExteriorSymmetricColumn.column 4) ExteriorFourthColumn.retract_column x

theorem retract211_project (x : Total (A := A)) :
    retract211 (ExteriorFourthColumn.project x).val=retract211 x := by
  change retract211 (x-ExteriorSymmetricColumn.column 4 (ExteriorFourthColumn.retract x))=retract211 x
  rw [map_sub, retract211_column, sub_zero]

theorem retractK22_project (x : Total (A := A)) :
    retractK22 (ExteriorFourthColumn.project x).val=retractK22 x := by
  change retractK22 (x-ExteriorSymmetricColumn.column 4 (ExteriorFourthColumn.retract x))=retractK22 x
  rw [map_sub, retractK22_column, sub_zero]

def complement : Tail (A := A) →ₗ[ℂ] ExteriorFourthColumn.Remainder (A := A) (B := B) :=
  ExteriorFourthColumn.project.comp
    (insert211.comp (LinearMap.fst ℂ _ _)+insertK22.comp (LinearMap.snd ℂ _ _))

def extract : ExteriorFourthColumn.Remainder (A := A) (B := B) →ₗ[ℂ] Tail (A := A) :=
  (retract211.prod retractK22).comp (ExteriorFourthColumn.Remainder (A := A) (B := B)).subtype

theorem complement_apply (x : Tail (A := A)) : complement (A := A) x=
    ExteriorFourthColumn.project (A := A) (B := B)
      (insert211 (A := A) x.1+insertK22 (A := A) x.2) := rfl

theorem extract_fst (x : ExteriorFourthColumn.Remainder (A := A) (B := B)) :
    (extract (A := A) x).1=retract211 x.val := rfl

theorem extract_snd (x : ExteriorFourthColumn.Remainder (A := A) (B := B)) :
    (extract (A := A) x).2=retractK22 x.val := rfl

theorem complement_left_inv (x : Tail (A := A)) : extract (A := A) (complement (A := A) x)=x := by
  apply Prod.ext
  · rw [extract_fst, complement_apply, retract211_project, map_add, retract211_insert211, retract211_insertK22, add_zero]
  · rw [extract_snd, complement_apply, retractK22_project, map_add, retractK22_insert211, retractK22_insertK22, zero_add]

theorem complement_right_inv [FiniteDimensional ℂ A]
    (x : ExteriorFourthColumn.Remainder (A := A) (B := B)) : complement (A := A) (extract (A := A) x)=x := by
  obtain ⟨v,hv⟩ := combine_surjective (A := A) x.val
  have hm := congrArg (retract211 (A := A)) hv
  simp only [combine_apply, map_add, retract211_column, retract211_insert211,
    retract211_insertK22, zero_add, add_zero] at hm
  have hl := congrArg (retractK22 (A := A)) hv
  simp only [combine_apply, map_add, retractK22_column, retractK22_insert211,
    retractK22_insertK22, zero_add] at hl
  have hp : ExteriorFourthColumn.project (A := A) (B := B) (insert211 (A := A) v.2.1)+
      ExteriorFourthColumn.project (A := A) (B := B) (insertK22 (A := A) v.2.2)=x := by
    have ht := congrArg (ExteriorFourthColumn.project (A := A) (B := B)) hv
    simpa only [combine_apply, map_add, project_column, zero_add, project_kernel] using ht
  rw [complement_apply (A := A), extract_fst (A := A), extract_snd (A := A), ← hm, ← hl, map_add]
  exact hp

/-- The two new branches identify the actual kernel of the previous
top-column retraction, using explicit projected insertions and contractions. -/
def complementEquivalence [FiniteDimensional ℂ A] : Tail (A := A) ≃ₗ[ℂ]
    ExteriorFourthColumn.Remainder (A := A) (B := B) where
  toLinearMap := complement
  invFun := extract
  left_inv := complement_left_inv
  right_inv := complement_right_inv

end
end Math.ExteriorFourthDoubletCauchy
