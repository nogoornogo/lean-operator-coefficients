import Math.LinearAlgebra.ExteriorSymmetricColumn
import Math.LinearAlgebra.ExteriorCubeDoubletSplit

/-! Cubic doublet Cauchy branching in arbitrary color dimension.
Universal contractions establish independence. Exhaustion uses a polynomial
identity in an arbitrary dimension, rather than a content-specific rank. -/
namespace Math.ExteriorCubeDoubletCauchy
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open ExteriorCubeHook ExteriorCubeDoublet
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev Top := (⋀[ℂ]^3 A) ⊗[ℂ] Sym[ℂ]^3 B
abbrev Domain := Top (A := A) × (Hook (V := A) ⊗[ℂ] B)
abbrev Total := ⋀[ℂ]^3 (A ⊗[ℂ] B)
@[reducible] local instance : AddCommGroup (Top (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (Hook (V := A) ⊗[ℂ] B) := inferInstance

def topRaw : Triple (A ⊗[ℂ] B) →ₗ[ℂ] Top (A := A) :=
  (TensorProduct.map
    (TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap)
    (TensorCubeMultilinear.fromMultilinear (SymmetricPower.tprod ℂ))).comp regroup.toLinearMap

@[simp] theorem topRaw_pure (a b c : A) (s t u : B) :
    topRaw ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] u)))=
      cube a b c ⊗ₜ[ℂ] SymmetricPower.tprod ℂ ![s,t,u] := rfl

def topRetract : Total (A := A) →ₗ[ℂ] Top (A := A) :=
  (6 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (AlternatingThree.alternating (TensorCubeMultilinear.toMultilinear topRaw))

theorem topRetract_diagonal (a : Fin 3 → A) (s : B) :
    topRetract (exteriorPower.ιMulti ℂ 3 (fun i => a i ⊗ₜ[ℂ] s))=
      exteriorPower.ιMulti ℂ 3 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ : Fin 3 => s) := by
  change (6 : ℂ)⁻¹ •
    exteriorPower.alternatingMapLinearEquiv
      (AlternatingThree.alternating (TensorCubeMultilinear.toMultilinear topRaw))
      (exteriorPower.ιMulti ℂ 3 (fun i => a i ⊗ₜ[ℂ] s))=_
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change (6 : ℂ)⁻¹ • AlternatingThree.raw
    (TensorCubeMultilinear.toMultilinear topRaw) (fun i => a i ⊗ₜ[ℂ] s)=_
  rw [AlternatingThree.raw_apply]
  simp only [TensorCubeMultilinear.toMultilinear,MultilinearMap.mk'_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,topRaw_pure]
  have hs : (![s,s,s] : Fin 3 → B)=(fun _ => s) := by ext i; fin_cases i <;> rfl
  rw [hs,cube_swap01 (a 0) (a 1) (a 2),cube_swap01 (a 1) (a 2) (a 0),
    cube_swap12 (a 0) (a 1) (a 2),cube_cycle (a 0) (a 1) (a 2),
    ← cube_cycle (a 1) (a 2) (a 0),cube_eta a]
  simp only [TensorProduct.neg_tmul]
  module

theorem top_retract_column (x : Top (A := A)) :
    topRetract (ExteriorSymmetricColumn.column 3 x)=x := by
  have h : (topRetract (A := A)).comp (ExteriorSymmetricColumn.column 3)=LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hx : ((topRetract (A := A)).comp (ExteriorSymmetricColumn.column 3)).comp
        ((TensorProduct.mk ℂ _ _).flip y)=
        (LinearMap.id : Top (A := A) →ₗ[ℂ] _).comp ((TensorProduct.mk ℂ _ _).flip y) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro a
      have hy : ((topRetract (A := A)).comp (ExteriorSymmetricColumn.column 3)).comp
          (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 3 a))=
          (LinearMap.id : Top (A := A) →ₗ[ℂ] _).comp
            (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 3 a)) := by
        apply SymmetricPurePowers.ext
        intro s
        change topRetract (ExteriorSymmetricColumn.column 3
          (exteriorPower.ιMulti ℂ 3 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => s)))=_
        rw [ExteriorSymmetricColumn.diagonal,topRetract_diagonal]
        rfl
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun hx x
  exact LinearMap.congr_fun h x

theorem hook_retract_column (x : Top (A := A)) :
    hookRetract (ExteriorSymmetricColumn.column 3 x)=0 := by
  have h : (hookRetract (A := A)).comp (ExteriorSymmetricColumn.column 3)=0 := by
    apply TensorProduct.ext'
    intro x y
    have hx : ((hookRetract (A := A)).comp (ExteriorSymmetricColumn.column 3)).comp
        ((TensorProduct.mk ℂ _ _).flip y)=0 := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro a
      change hookRetract (ExteriorSymmetricColumn.column 3
        (exteriorPower.ιMulti ℂ 3 a ⊗ₜ[ℂ] y))=0
      rw [ExteriorSymmetricColumn.column_pure]
      change (9 : ℂ)⁻¹ • TensorProduct.map project LinearMap.id
        (contract (TopExteriorCauchy.map a y))=0
      rw [ExteriorCubeDoubletSplit.contract_column,map_zero,smul_zero]
    exact LinearMap.congr_fun hx x
  exact LinearMap.congr_fun h x

def combine : Domain (A := A) →ₗ[ℂ] Total (A := A) :=
  (ExteriorSymmetricColumn.column 3).comp (LinearMap.fst ℂ _ _)+
    hookInsert.comp (LinearMap.snd ℂ _ _)

theorem combine_injective : Function.Injective (combine (A := A)) := by
  intro x y hxy
  have hs := congrArg hookRetract hxy
  change hookRetract (ExteriorSymmetricColumn.column 3 x.1+hookInsert x.2)=
    hookRetract (ExteriorSymmetricColumn.column 3 y.1+hookInsert y.2) at hs
  rw [map_add,map_add,hook_retract_column,hook_retract_column,hook_retract_insert,
    hook_retract_insert,zero_add,zero_add] at hs
  apply Prod.ext _ hs
  change ExteriorSymmetricColumn.column 3 x.1+hookInsert x.2=
    ExteriorSymmetricColumn.column 3 y.1+hookInsert y.2 at hxy
  rw [hs] at hxy
  have ht := congrArg topRetract (add_right_cancel hxy)
  simpa only [top_retract_column] using ht

/-- The exhaustion identity holds in every dimension. Its hypothesis is
exactly the dimension relation from the universal hook split. -/
theorem binomial_identity (n k : ℕ) (hk : n * n.choose 2 = n.choose 3+k) :
    4 * n.choose 3+2*k=(2*n).choose 3 := by
  have h2 := Nat.descFactorial_eq_factorial_mul_choose n 2
  have h3 := Nat.descFactorial_eq_factorial_mul_choose n 3
  have ht := Nat.descFactorial_eq_factorial_mul_choose (2*n) 3
  rcases n with _ | _ | n
  · simpa using hk.symm
  · simpa using hk.symm
  · simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.mul_one,
      Nat.factorial_succ,Nat.factorial_zero] at h2 h3 ht
    have e1 : n+1+1-1=n+1 := by omega
    have e2 : n+1+1-2=n := by omega
    have e3 : 2*(n+1+1)-1=2*n+3 := by omega
    have e4 : 2*(n+1+1)-2=2*n+2 := by omega
    simp only [Nat.sub_zero,e1,e2,e3,e4] at h2 h3 ht
    have hh := congrArg (fun x => (n+1+1)*x) h2
    nlinarith

theorem dimensions [FiniteDimensional ℂ A] :
    Module.finrank ℂ (Domain (A := A))=Module.finrank ℂ (Total (A := A)) := by
  have he := (ExteriorCubeHook.split (V := A)).finrank_eq
  rw [Module.finrank_tensorProduct,Module.finrank_prod,
    exteriorPower.finrank_eq,exteriorPower.finrank_eq] at he
  change Module.finrank ℂ ((Top (A := A)) × (Hook (V := A) ⊗[ℂ] B))=_
  rw [Module.finrank_prod,Module.finrank_tensorProduct,Module.finrank_tensorProduct,
    exteriorPower.finrank_eq,SymmetricPower.finrank_eq,exteriorPower.finrank_eq,
    Module.finrank_tensorProduct]
  have hb : Module.finrank ℂ B=2 := by simp [B,WeakDoubletScalars.Doublet]
  rw [hb]
  norm_num [Nat.multichoose,Nat.choose]
  simpa only [Nat.mul_comm] using binomial_identity (Module.finrank ℂ A)
    (Module.finrank ℂ (Hook (V := A))) he

theorem combine_surjective [FiniteDimensional ℂ A] :
    Function.Surjective (combine (A := A)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (dimensions (A := A))).mp
    combine_injective

/-- Complete cubic Cauchy branching for any finite-dimensional A. -/
def equivalence [FiniteDimensional ℂ A] : Domain (A := A) ≃ₗ[ℂ] Total (A := A) :=
  LinearEquiv.ofBijective combine ⟨combine_injective,combine_surjective⟩

end
end Math.ExteriorCubeDoubletCauchy
