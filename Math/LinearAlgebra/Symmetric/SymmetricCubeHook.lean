import Math.LinearAlgebra.Exterior.ExteriorCubeHook
import Math.LinearAlgebra.Tensor.TensorCubeMultilinear
import Math.LinearAlgebra.Symmetric.SymmetricPurePowers
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-! The symmetric cubic quotient and the actual exterior-hook complement.
All identities are universal vector identities, with no finite dimension,
irreducibility or representation multiplicity premise. -/
namespace Math.SymmetricCubeHook
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev Source := A ⊗[ℂ] Sym[ℂ]^2 A
abbrev Triple := A ⊗[ℂ] (A ⊗[ℂ] A)
@[reducible] local instance : AddCommGroup (Source (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Source (V := A)) := inferInstance

def swapFirst : Triple (A := A) →ₗ[ℂ] Triple (A := A) :=
  TensorCubeMultilinear.fromMultilinear
    ((TensorCubeMultilinear.toMultilinear (LinearMap.id : Triple (A := A) →ₗ[ℂ] _)).domDomCongr
      (Equiv.swap 0 1))

@[simp] theorem swapFirst_pure (a b c : A) :
    swapFirst (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c))=b ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] c) := rfl

def toSymmetric : ExteriorCubeHook.Source (V := A) →ₗ[ℂ] Source (A := A) :=
  (TensorProduct.map LinearMap.id sym).comp
    (swapFirst.comp (TensorProduct.map LinearMap.id alternatingSection))

def toExterior : Source (A := A) →ₗ[ℂ] ExteriorCubeHook.Source (V := A) :=
  (TensorProduct.map LinearMap.id wedge).comp
    (swapFirst.comp (TensorProduct.map LinearMap.id symmetricSection))

@[simp] theorem toSymmetric_pure (a b c : A) :
    toSymmetric (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c))=
      b ⊗ₜ[ℂ] sym (a ⊗ₜ[ℂ] c)-c ⊗ₜ[ℂ] sym (a ⊗ₜ[ℂ] b) := by
  simp only [toSymmetric,LinearMap.comp_apply,TensorProduct.map_tmul,
    alternatingSection_pure,LinearMap.id_apply,TensorProduct.tmul_sub,map_sub,swapFirst_pure]

@[simp] theorem toExterior_pure (a b c : A) :
    toExterior (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c))=
      b ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] c)+c ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b) := by
  simp only [toExterior,LinearMap.comp_apply,TensorProduct.map_tmul,
    symmetricSection_pure,LinearMap.id_apply,TensorProduct.tmul_add,map_add,swapFirst_pure]

def multiply : Source (A := A) →ₗ[ℂ] Sym[ℂ]^3 A :=
  (2 : ℂ)⁻¹ • (TensorCubeMultilinear.fromMultilinear (SymmetricPower.tprod ℂ)).comp
    (TensorProduct.map LinearMap.id symmetricSection)

theorem symCube_swap12 (a b c : A) :
    SymmetricPower.tprod ℂ ![a,c,b]=SymmetricPower.tprod ℂ ![a,b,c] := by
  have h := SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap (1 : Fin 3) 2) ![a,b,c]
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem multiply_pure (a b c : A) :
    multiply (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c))=SymmetricPower.tprod ℂ ![a,b,c] := by
  simp only [multiply,LinearMap.smul_apply,LinearMap.comp_apply,TensorProduct.map_tmul,
    LinearMap.id_apply,symmetricSection_pure,TensorProduct.tmul_add,map_add,
    TensorCubeMultilinear.from_pure,symCube_swap12]
  module

def raw : MultilinearMap ℂ (fun _ : Fin 3 => A) (Source (A := A)) :=
  MultilinearMap.mk' (fun v => v 0 ⊗ₜ[ℂ] sym (v 1 ⊗ₜ[ℂ] v 2)+
    v 1 ⊗ₜ[ℂ] sym (v 0 ⊗ₜ[ℂ] v 2)+v 2 ⊗ₜ[ℂ] sym (v 0 ⊗ₜ[ℂ] v 1))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update,TensorProduct.add_tmul,TensorProduct.tmul_add,map_add] <;> module)
    (by intro v i z x; fin_cases i <;>
      simp [Function.update,TensorProduct.smul_tmul,TensorProduct.tmul_smul,map_smul,smul_add])

theorem raw_apply (v : Fin 3 → A) : raw v=v 0 ⊗ₜ[ℂ] sym (v 1 ⊗ₜ[ℂ] v 2)+
    v 1 ⊗ₜ[ℂ] sym (v 0 ⊗ₜ[ℂ] v 2)+v 2 ⊗ₜ[ℂ] sym (v 0 ⊗ₜ[ℂ] v 1) := rfl

theorem raw_symmetric (e : Equiv.Perm (Fin 3)) (v : Fin 3 → A) : raw (v ∘ e)=raw v := by
  rw [raw_apply,raw_apply]
  have h01 := sym_swap (v 0) (v 1)
  have h02 := sym_swap (v 0) (v 2)
  have h12 := sym_swap (v 1) (v 2)
  have hr (i : Fin 3) : finRotate 3 i=(![1,2,0] : Fin 3 → Fin 3) i := by
    fin_cases i <;> rfl
  have hi (i : Fin 3) : (finRotate 3)⁻¹ i=(![2,0,1] : Fin 3 → Fin 3) i := by
    fin_cases i <;> rfl
  rcases e.fin_three_cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Function.comp_apply,Equiv.swap_apply_def,hr,hi]
  all_goals norm_num [h01,h02,h12]
  all_goals abel

def coproduct : Sym[ℂ]^3 A →ₗ[ℂ] Source (A := A) :=
  SymmetricPowerDescent.lift 3 ⟨raw,raw_symmetric⟩

@[simp] theorem coproduct_pure (a b c : A) :
    coproduct (SymmetricPower.tprod ℂ ![a,b,c])=
      a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)+b ⊗ₜ[ℂ] sym (a ⊗ₜ[ℂ] c)+
        c ⊗ₜ[ℂ] sym (a ⊗ₜ[ℂ] b) := by
  rw [coproduct,SymmetricPowerDescent.lift_tprod]
  rfl

theorem source_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Source (A := A) →ₗ[ℂ] N}
    (h : ∀ a b c, f (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c))=
      g (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c))) : f=g := by
  apply TensorProduct.ext'
  intro a x
  have ha : f.comp (TensorProduct.mk ℂ _ _ a)=g.comp (TensorProduct.mk ℂ _ _ a) := by
    apply SymmetricPower.ext
    intro v
    change f (a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ v)=g (a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ v)
    rw [← sym_eta v]
    exact h a (v 0) (v 1)
  exact LinearMap.congr_fun ha x

theorem toSymmetric_toExterior : (toSymmetric (A := A)).comp toExterior=
    (3 : ℂ) • LinearMap.id-coproduct.comp multiply := by
  apply source_ext
  intro a b c
  change toSymmetric (toExterior (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))=
    (3 : ℂ) • (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c))-
      coproduct (multiply (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))
  rw [toExterior_pure,map_add,toSymmetric_pure,toSymmetric_pure,multiply_pure,coproduct_pure]
  simp only [sym_swap]
  module

theorem exterior_source_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : ExteriorCubeHook.Source (V := A) →ₗ[ℂ] N}
    (h : ∀ a b c, f (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c))=
      g (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c))) : f=g := by
  apply TensorProduct.ext'
  intro a x
  have ha : f.comp (TensorProduct.mk ℂ _ _ a)=g.comp (TensorProduct.mk ℂ _ _ a) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change f (a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v)=g (a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v)
    rw [← wedge_eta v]
    exact h a (v 0) (v 1)
  exact LinearMap.congr_fun ha x

theorem toExterior_toSymmetric : (toExterior (A := A)).comp toSymmetric=
    (3 : ℂ) • LinearMap.id-ExteriorCubeHook.coproduct.comp ExteriorCubeHook.multiply := by
  apply exterior_source_ext
  intro a b c
  change toExterior (toSymmetric (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)))=
    (3 : ℂ) • (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c))-
      ExteriorCubeHook.coproduct (ExteriorCubeHook.multiply (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)))
  rw [toSymmetric_pure,map_sub,toExterior_pure,toExterior_pure,
    ExteriorCubeHook.multiply_pure,ExteriorCubeHook.coproduct_pure]
  rw [ExteriorSquareTensorDescent.wedge_swap a b,
    ExteriorSquareTensorDescent.wedge_swap a c,
    ExteriorSquareTensorDescent.wedge_swap b c]
  simp only [TensorProduct.tmul_neg]
  module

theorem exterior_multiply_toExterior (x : Source (A := A)) :
    ExteriorCubeHook.multiply (toExterior x)=0 := by
  have h : (ExteriorCubeHook.multiply (V := A)).comp toExterior=0 := by
    apply source_ext
    intro a b c
    change ExteriorCubeHook.multiply (toExterior (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))=0
    rw [toExterior_pure,map_add,ExteriorCubeHook.multiply_pure,
      ExteriorCubeHook.multiply_pure,ExteriorCubeHook.cube_swap01 a b c,
      ExteriorCubeHook.cube_cycle a b c,neg_add_cancel]
  exact LinearMap.congr_fun h x

theorem symCube_swap01 (a b c : A) :
    SymmetricPower.tprod ℂ ![b,a,c]=SymmetricPower.tprod ℂ ![a,b,c] := by
  have h := SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap (0 : Fin 3) 1) ![a,b,c]
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply_toSymmetric (x : ExteriorCubeHook.Source (V := A)) :
    multiply (toSymmetric x)=0 := by
  have h : (multiply (A := A)).comp toSymmetric=0 := by
    apply exterior_source_ext
    intro a b c
    change multiply (toSymmetric (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)))=0
    rw [toSymmetric_pure,map_sub,multiply_pure,multiply_pure,
      symCube_swap01 a b c,symCube_swap01 a c b,symCube_swap12 a b c,sub_self]
  exact LinearMap.congr_fun h x

theorem power_diagonal (a : A) : SymmetricPower.tprod ℂ (fun _ : Fin 3 => a)=
    SymmetricPower.tprod ℂ ![a,a,a] := by
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply_coproduct (x : Sym[ℂ]^3 A) : multiply (coproduct x)=(3 : ℂ) • x := by
  have h : (multiply (A := A)).comp coproduct=(3 : ℂ) • LinearMap.id := by
    apply SymmetricPurePowers.ext
    intro a
    change multiply (coproduct (SymmetricPower.tprod ℂ (fun _ : Fin 3 => a)))=
      (3 : ℂ) • SymmetricPower.tprod ℂ (fun _ : Fin 3 => a)
    rw [power_diagonal,coproduct_pure,map_add,map_add,multiply_pure]
    module
  exact LinearMap.congr_fun h x

theorem toExterior_coproduct (x : Sym[ℂ]^3 A) : toExterior (coproduct x)=0 := by
  have h : (toExterior (A := A)).comp coproduct=0 := by
    apply SymmetricPurePowers.ext
    intro a
    change toExterior (coproduct (SymmetricPower.tprod ℂ (fun _ : Fin 3 => a)))=0
    rw [power_diagonal,coproduct_pure,map_add,map_add,toExterior_pure,
      ExteriorCubeHook.wedge_self,TensorProduct.tmul_zero,zero_add,zero_add,zero_add]
  exact LinearMap.congr_fun h x

def toHook : Source (A := A) →ₗ[ℂ] ExteriorCubeHook.Hook (V := A) :=
  toExterior.codRestrict _ exterior_multiply_toExterior

/-- Universal symmetric-cube/exterior-hook splitting, with explicit inverses. -/
def split : Source (A := A) ≃ₗ[ℂ] (Sym[ℂ]^3 A) × ExteriorCubeHook.Hook (V := A) where
  toLinearMap := multiply.prod ((3 : ℂ)⁻¹ • toHook)
  invFun x := (3 : ℂ)⁻¹ • coproduct x.1+toSymmetric x.2.val
  left_inv x := by
    change (3 : ℂ)⁻¹ • coproduct (multiply x)+toSymmetric ((3 : ℂ)⁻¹ • toExterior x)=x
    have h := LinearMap.congr_fun (toSymmetric_toExterior (A := A)) x
    change toSymmetric (toExterior x)=(3 : ℂ) • x-coproduct (multiply x) at h
    rw [map_smul,h,smul_sub,smul_smul]
    norm_num
  right_inv x := by
    apply Prod.ext
    · change multiply ((3 : ℂ)⁻¹ • coproduct x.1+toSymmetric x.2.val)=x.1
      rw [map_add,map_smul,multiply_coproduct,multiply_toSymmetric,add_zero,smul_smul]
      norm_num
    · apply Subtype.ext
      change (3 : ℂ)⁻¹ • toExterior ((3 : ℂ)⁻¹ • coproduct x.1+toSymmetric x.2.val)=x.2.val
      have h := LinearMap.congr_fun (toExterior_toSymmetric (A := A)) x.2.val
      change toExterior (toSymmetric x.2.val)=(3 : ℂ) • x.2.val-
        ExteriorCubeHook.coproduct (ExteriorCubeHook.multiply x.2.val) at h
      rw [show ExteriorCubeHook.multiply x.2.val=0 from x.2.property,
        map_zero,sub_zero] at h
      rw [map_add,map_smul,toExterior_coproduct,smul_zero,zero_add,h,smul_smul]
      norm_num

theorem sym_natural (f : A →ₗ[ℂ] A) (a b : A) :
    sym (f a ⊗ₜ[ℂ] f b)=SymmetricPower.map (ι := Fin 2) f (sym (a ⊗ₜ[ℂ] b)) := by
  rw [sym_tmul,sym_tmul,SymmetricPower.map_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem symCube_natural (f : A →ₗ[ℂ] A) (a b c : A) :
    SymmetricPower.tprod ℂ ![f a,f b,f c]=
      SymmetricPower.map (ι := Fin 3) f (SymmetricPower.tprod ℂ ![a,b,c]) := by
  rw [SymmetricPower.map_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply_natural (f : A →ₗ[ℂ] A) (x : Source (A := A)) :
    multiply (TensorProduct.map f (SymmetricPower.map (ι := Fin 2) f) x)=
      SymmetricPower.map (ι := Fin 3) f (multiply x) := by
  have h : (multiply (A := A)).comp
      (TensorProduct.map f (SymmetricPower.map (ι := Fin 2) f))=
      (SymmetricPower.map (ι := Fin 3) f).comp multiply := by
    apply source_ext
    intro a b c
    change multiply (TensorProduct.map f (SymmetricPower.map (ι := Fin 2) f)
      (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))=
      SymmetricPower.map (ι := Fin 3) f (multiply (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))
    rw [TensorProduct.map_tmul,← sym_natural,multiply_pure,multiply_pure,symCube_natural]
  exact LinearMap.congr_fun h x

theorem toExterior_natural (f : A →ₗ[ℂ] A) (x : Source (A := A)) :
    toExterior (TensorProduct.map f (SymmetricPower.map (ι := Fin 2) f) x)=
      TensorProduct.map f (exteriorPower.map 2 f) (toExterior x) := by
  have h : (toExterior (A := A)).comp
      (TensorProduct.map f (SymmetricPower.map (ι := Fin 2) f))=
      (TensorProduct.map f (exteriorPower.map 2 f)).comp toExterior := by
    apply source_ext
    intro a b c
    change toExterior (TensorProduct.map f (SymmetricPower.map (ι := Fin 2) f)
      (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))=
      TensorProduct.map f (exteriorPower.map 2 f) (toExterior (a ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] c)))
    rw [TensorProduct.map_tmul,← sym_natural,toExterior_pure,toExterior_pure]
    simp only [map_add,TensorProduct.map_tmul,← ExteriorCubeHook.wedge_natural]
  exact LinearMap.congr_fun h x

end
end Math.SymmetricCubeHook
