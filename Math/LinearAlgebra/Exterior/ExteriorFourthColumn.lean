import Math.LinearAlgebra.Exterior.ExteriorSymmetricColumn
import Math.LinearAlgebra.Tensor.TensorFourthMultilinear
import Math.LinearAlgebra.Exterior.ExteriorFourthKernels
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! An actual split embedding of the quartic exterior/symmetric column.
The universal alternator stays symbolic; no representation basis is expanded. -/
namespace Math.ExteriorFourthColumn
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorFourthMultilinear

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
abbrev Column := (⋀[ℂ]^4 A) ⊗[ℂ] Sym[ℂ]^4 B
abbrev Total := ⋀[ℂ]^4 (A ⊗[ℂ] B)
@[reducible] local instance : AddCommGroup (Column (A := A) (B := B)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def regroupThree :
    (A ⊗[ℂ] B) ⊗[ℂ] ((A ⊗[ℂ] B) ⊗[ℂ] (A ⊗[ℂ] B)) ≃ₗ[ℂ]
      (A ⊗[ℂ] (A ⊗[ℂ] A)) ⊗[ℂ] (B ⊗[ℂ] (B ⊗[ℂ] B)) :=
  (TensorProduct.congr (.refl ℂ _) (TensorProduct.tensorTensorTensorComm ℂ A B A B)).trans
    (TensorProduct.tensorTensorTensorComm ℂ A B (A ⊗[ℂ] A) (B ⊗[ℂ] B))

def regroup : Tensor (V := A ⊗[ℂ] B) ≃ₗ[ℂ] Tensor (V := A) ⊗[ℂ] Tensor (V := B) :=
  (TensorProduct.congr (.refl ℂ _) regroupThree).trans
    (TensorProduct.tensorTensorTensorComm ℂ A B
      (A ⊗[ℂ] (A ⊗[ℂ] A)) (B ⊗[ℂ] (B ⊗[ℂ] B)))

def raw : Tensor (V := A ⊗[ℂ] B) →ₗ[ℂ] Column (A := A) (B := B) :=
  (TensorProduct.map (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap)
    (fromMultilinear (SymmetricPower.tprod ℂ))).comp regroup.toLinearMap

@[simp] theorem raw_pure (a b c d : A) (s t u v : B) :
    raw ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ]
      ((c ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] v))))=
      exteriorPower.ιMulti ℂ 4 ![a,b,c,d] ⊗ₜ[ℂ] SymmetricPower.tprod ℂ ![s,t,u,v] := rfl

theorem raw_diagonal (a : Fin 4 → A) (s : B) :
    toMultilinear (raw (A := A) (B := B)) (fun i => a i ⊗ₜ[ℂ] s)=
      exteriorPower.ιMulti ℂ 4 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ : Fin 4 => s) := by
  change exteriorPower.ιMulti ℂ 4 ![a 0,a 1,a 2,a 3] ⊗ₜ[ℂ]
    SymmetricPower.tprod ℂ ![s,s,s,s]=_
  congr 2 <;> ext i <;> fin_cases i <;> rfl

def retract : Total (A := A) (B := B) →ₗ[ℂ] Column (A := A) (B := B) :=
  (24 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (toMultilinear (raw (A := A) (B := B))).alternatization

theorem retract_diagonal (a : Fin 4 → A) (s : B) :
    retract (exteriorPower.ιMulti ℂ 4 (fun i => a i ⊗ₜ[ℂ] s))=
      exteriorPower.ιMulti ℂ 4 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ : Fin 4 => s) := by
  change (24 : ℂ)⁻¹ • exteriorPower.alternatingMapLinearEquiv
    (toMultilinear (raw (A := A) (B := B))).alternatization
    (exteriorPower.ιMulti ℂ 4 (fun i => a i ⊗ₜ[ℂ] s))=_
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, MultilinearMap.alternatization_apply]
  have he (σ : Equiv.Perm (Fin 4)) :
      Equiv.Perm.sign σ • (toMultilinear (raw (A := A) (B := B))).domDomCongr σ
        (fun i => a i ⊗ₜ[ℂ] s)=
        exteriorPower.ιMulti ℂ 4 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ : Fin 4 => s) := by
    change Equiv.Perm.sign σ • toMultilinear (raw (A := A) (B := B))
      (fun i => a (σ i) ⊗ₜ[ℂ] s)=_
    rw [raw_diagonal]
    change Equiv.Perm.sign σ • (exteriorPower.ιMulti ℂ 4 (a ∘ σ) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin 4 => s))=_
    rw [(exteriorPower.ιMulti ℂ 4).map_perm a σ]
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
      ← TensorProduct.smul_tmul', smul_smul, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

theorem retract_column (x : Column (A := A) (B := B)) :
    retract (ExteriorSymmetricColumn.column 4 x)=x := by
  have h : (retract (A := A) (B := B)).comp (ExteriorSymmetricColumn.column 4)=LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hx : ((retract (A := A) (B := B)).comp (ExteriorSymmetricColumn.column 4)).comp
        ((TensorProduct.mk ℂ _ _).flip y)=
        (LinearMap.id : Column (A := A) (B := B) →ₗ[ℂ] _).comp
          ((TensorProduct.mk ℂ _ _).flip y) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro a
      have hy : ((retract (A := A) (B := B)).comp (ExteriorSymmetricColumn.column 4)).comp
          (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 4 a))=
          (LinearMap.id : Column (A := A) (B := B) →ₗ[ℂ] _).comp
            (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 4 a)) := by
        apply SymmetricPurePowers.ext
        intro s
        change retract (ExteriorSymmetricColumn.column 4
          (exteriorPower.ιMulti ℂ 4 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => s)))=_
        rw [ExteriorSymmetricColumn.diagonal,retract_diagonal]
        rfl
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun hx x
  exact LinearMap.congr_fun h x

theorem column_injective : Function.Injective
    (ExteriorSymmetricColumn.column (A := A) (B := B) 4) :=
  Function.LeftInverse.injective retract_column

abbrev Remainder := LinearMap.ker (retract (A := A) (B := B))

def project : Total (A := A) (B := B) →ₗ[ℂ] Remainder (A := A) (B := B) :=
  SectionKernel.project retract (ExteriorSymmetricColumn.column 4) retract_column

/-- This isolates the proved top column; identifying the remainder with
K211 tensor Sym² B plus K22 is a separate obligation for a doublet B. -/
def split : Total (A := A) (B := B) ≃ₗ[ℂ]
    Column (A := A) (B := B) × Remainder (A := A) (B := B) :=
  SectionKernel.equivalence retract (ExteriorSymmetricColumn.column 4) retract_column

def tensorMap {V : Type*} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) :
    Tensor (V := V) →ₗ[ℂ] Tensor (V := V) :=
  TensorProduct.map f (TensorProduct.map f (TensorProduct.map f f))

theorem raw_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) :
    (raw (A := A) (B := B)).comp (tensorMap (TensorProduct.map f g))=
      (TensorProduct.map (exteriorPower.map 4 f) (SymmetricPower.map (ι := Fin 4) g)).comp raw := by
  ext a s b t c u d v
  change exteriorPower.ιMulti ℂ 4 ![f a,f b,f c,f d] ⊗ₜ[ℂ]
    SymmetricPower.tprod ℂ ![g s,g t,g u,g v]=
    exteriorPower.map 4 f (exteriorPower.ιMulti ℂ 4 ![a,b,c,d]) ⊗ₜ[ℂ]
      SymmetricPower.map (ι := Fin 4) g (SymmetricPower.tprod ℂ ![s,t,u,v])
  rw [exteriorPower.map_apply_ιMulti, SymmetricPower.map_tprod]
  congr 2 <;> ext i <;> fin_cases i <;> rfl

theorem raw_multilinear_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) :
    (toMultilinear (raw (A := A) (B := B))).compLinearMap (fun _ => TensorProduct.map f g)=
      (TensorProduct.map (exteriorPower.map 4 f) (SymmetricPower.map (ι := Fin 4) g)).compMultilinearMap
        (toMultilinear raw) := by
  apply MultilinearMap.ext
  intro v
  exact LinearMap.congr_fun (raw_natural f g)
    (v 0 ⊗ₜ[ℂ] (v 1 ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)))

theorem retract_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) (x : Total (A := A) (B := B)) :
    retract (exteriorPower.map 4 (TensorProduct.map f g) x)=
      TensorProduct.map (exteriorPower.map 4 f) (SymmetricPower.map (ι := Fin 4) g) (retract x) := by
  have ha := congrArg MultilinearMap.alternatization (raw_multilinear_natural f g)
  rw [MultilinearMap.alternatization_compLinearMap,
    LinearMap.compMultilinearMap_alternatization] at ha
  have h : (retract (A := A) (B := B)).comp (exteriorPower.map 4 (TensorProduct.map f g))=
      (TensorProduct.map (exteriorPower.map 4 f) (SymmetricPower.map (ι := Fin 4) g)).comp retract := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change retract (exteriorPower.map 4 (TensorProduct.map f g) (exteriorPower.ιMulti ℂ 4 v))=
      TensorProduct.map (exteriorPower.map 4 f) (SymmetricPower.map (ι := Fin 4) g)
        (retract (exteriorPower.ιMulti ℂ 4 v))
    simp only [retract, LinearMap.smul_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_smul]
    exact congrArg (fun z => (24 : ℂ)⁻¹ • z) (DFunLike.congr_fun ha v)
  exact LinearMap.congr_fun h x

end
end Math.ExteriorFourthColumn
