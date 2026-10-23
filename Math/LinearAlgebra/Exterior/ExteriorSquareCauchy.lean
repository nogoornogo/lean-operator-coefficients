import Math.LinearAlgebra.Tensor.TensorSquareQuotients
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! The complete exterior-square Cauchy decomposition by explicit inverse
maps, independent of bases, dimensions or irreducibility assumptions. -/
namespace Math.ExteriorSquareCauchy
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients

@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
abbrev First := (⋀[ℂ]^2 A) ⊗[ℂ] Sym[ℂ]^2 B
abbrev Second := (Sym[ℂ]^2 A) ⊗[ℂ] ⋀[ℂ]^2 B
abbrev Total := ⋀[ℂ]^2 (A ⊗[ℂ] B)

@[reducible] local instance : AddCommGroup (First (A := A) (B := B)) := inferInstance
@[reducible] local instance : AddCommGroup (Second (A := A) (B := B)) := inferInstance
@[reducible] local instance : AddCommGroup (Total (A := A) (B := B)) := inferInstance

def regroup := TensorProduct.tensorTensorTensorComm ℂ A B A B

@[simp] theorem regroup_symm_pure (a c : A) (b d : B) :
    (regroup (A := A) (B := B)).symm ((a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] d))=
      (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d) := rfl

def rawFirst : ((A ⊗[ℂ] B) ⊗[ℂ] (A ⊗[ℂ] B)) →ₗ[ℂ] First (A := A) (B := B) :=
  (TensorProduct.map wedge sym).comp regroup.toLinearMap

def rawSecond : ((A ⊗[ℂ] B) ⊗[ℂ] (A ⊗[ℂ] B)) →ₗ[ℂ] Second (A := A) (B := B) :=
  (TensorProduct.map sym wedge).comp regroup.toLinearMap

@[simp] theorem rawFirst_pure (a c : A) (b d : B) :
    rawFirst ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))=
      wedge (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] d) := rfl
@[simp] theorem rawSecond_pure (a c : A) (b d : B) :
    rawSecond ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))=
      sym (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] d) := rfl

theorem rawFirst_anti (x y : A ⊗[ℂ] B) : rawFirst (y ⊗ₜ[ℂ] x) = -rawFirst (x ⊗ₜ[ℂ] y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add,hx,hz]; exact (neg_add _ _).symm
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add,hy,hz]; exact (neg_add _ _).symm
    | tmul c d =>
      rw [rawFirst_pure,rawFirst_pure,ExteriorSquareTensorDescent.wedge_swap a c,sym_swap b d,
        TensorProduct.neg_tmul]

theorem rawSecond_anti (x y : A ⊗[ℂ] B) : rawSecond (y ⊗ₜ[ℂ] x) = -rawSecond (x ⊗ₜ[ℂ] y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add,hx,hz]; exact (neg_add _ _).symm
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add,hy,hz]; exact (neg_add _ _).symm
    | tmul c d =>
      rw [rawSecond_pure,rawSecond_pure,sym_swap a c,ExteriorSquareTensorDescent.wedge_swap b d,
        TensorProduct.tmul_neg]

def first : Total (A := A) (B := B) →ₗ[ℂ] First (A := A) (B := B) :=
  ExteriorSquareTensorDescent.equiv ⟨rawFirst,fun x y => rawFirst_anti x y⟩
def second : Total (A := A) (B := B) →ₗ[ℂ] Second (A := A) (B := B) :=
  ExteriorSquareTensorDescent.equiv ⟨rawSecond,fun x y => rawSecond_anti x y⟩

@[simp] theorem first_wedge (x y : A ⊗[ℂ] B) : first (wedge (x ⊗ₜ[ℂ] y))=rawFirst (x ⊗ₜ[ℂ] y) :=
  ExteriorSquareTensorDescent.equiv_apply _ _
@[simp] theorem second_wedge (x y : A ⊗[ℂ] B) : second (wedge (x ⊗ₜ[ℂ] y))=rawSecond (x ⊗ₜ[ℂ] y) :=
  ExteriorSquareTensorDescent.equiv_apply _ _

def left : First (A := A) (B := B) →ₗ[ℂ] Total (A := A) (B := B) :=
  wedge.comp (regroup.symm.toLinearMap.comp (TensorProduct.map alternatingSection symmetricSection))
def right : Second (A := A) (B := B) →ₗ[ℂ] Total (A := A) (B := B) :=
  wedge.comp (regroup.symm.toLinearMap.comp (TensorProduct.map symmetricSection alternatingSection))

@[simp] theorem left_pure (a c : A) (b d : B) :
    left (wedge (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] sym (b ⊗ₜ[ℂ] d))=
      wedge ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))+
      wedge ((a ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] b))-
      wedge ((c ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] d))-
      wedge ((c ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) := by
  simp only [left,LinearMap.comp_apply,TensorProduct.map_tmul,alternatingSection_pure,symmetricSection_pure]
  simp only [TensorProduct.sub_tmul,TensorProduct.tmul_add,map_add,map_sub]
  simp only [LinearEquiv.coe_coe,regroup_symm_pure]
  module

@[simp] theorem right_pure (a c : A) (b d : B) :
    right (sym (a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] d))=
      wedge ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))-
      wedge ((a ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] b))+
      wedge ((c ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] d))-
      wedge ((c ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) := by
  simp only [right,LinearMap.comp_apply,TensorProduct.map_tmul,symmetricSection_pure,alternatingSection_pure]
  simp only [TensorProduct.add_tmul,TensorProduct.tmul_sub,map_add,map_sub]
  simp only [LinearEquiv.coe_coe,regroup_symm_pure]
  module

theorem first_left (x : First (A := A) (B := B)) : first (left x)=(4 : ℂ) • x := by
  have h : (first (A := A) (B := B)).comp left=(4 : ℂ) • LinearMap.id := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply SymmetricPower.ext
    intro w
    change first (left (exteriorPower.ιMulti ℂ 2 v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w))=
      (4 : ℂ) • (exteriorPower.ιMulti ℂ 2 v ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)
    rw [← wedge_eta v,← sym_eta w]
    simp only [left_pure,map_add,map_sub,first_wedge,rawFirst_pure,
      ExteriorSquareTensorDescent.wedge_swap (v 0) (v 1),sym_swap (w 0) (w 1),TensorProduct.neg_tmul]
    module
  exact LinearMap.congr_fun h x

theorem second_left (x : First (A := A) (B := B)) : second (left x)=0 := by
  have h : (second (A := A) (B := B)).comp left=0 := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply SymmetricPower.ext
    intro w
    change second (left (wedge (v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] sym (w 0 ⊗ₜ[ℂ] w 1)))=0
    simp only [left_pure,map_add,map_sub,second_wedge,rawSecond_pure,
      sym_swap (v 0) (v 1),ExteriorSquareTensorDescent.wedge_swap (w 0) (w 1),TensorProduct.tmul_neg]
    module
  exact LinearMap.congr_fun h x

theorem first_right (x : Second (A := A) (B := B)) : first (right x)=0 := by
  have h : (first (A := A) (B := B)).comp right=0 := by
    apply TensorProduct.ext
    apply SymmetricPower.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change first (right (sym (v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] wedge (w 0 ⊗ₜ[ℂ] w 1)))=0
    simp only [right_pure,map_add,map_sub,first_wedge,rawFirst_pure,
      ExteriorSquareTensorDescent.wedge_swap (v 0) (v 1),sym_swap (w 0) (w 1),TensorProduct.neg_tmul]
    module
  exact LinearMap.congr_fun h x

theorem second_right (x : Second (A := A) (B := B)) : second (right x)=(4 : ℂ) • x := by
  have h : (second (A := A) (B := B)).comp right=(4 : ℂ) • LinearMap.id := by
    apply TensorProduct.ext
    apply SymmetricPower.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change second (right (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 w))=
      (4 : ℂ) • (SymmetricPower.tprod ℂ v ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 w)
    rw [← sym_eta v,← wedge_eta w]
    simp only [right_pure,map_add,map_sub,second_wedge,rawSecond_pure,
      sym_swap (v 0) (v 1),ExteriorSquareTensorDescent.wedge_swap (w 0) (w 1),TensorProduct.tmul_neg]
    module
  exact LinearMap.congr_fun h x

theorem reconstruct (x : Total (A := A) (B := B)) : left (first x)+right (second x)=(4 : ℂ) • x := by
  have h : (left (A := A) (B := B)).comp (first.comp wedge)+right.comp (second.comp wedge)=
      (4 : ℂ) • wedge := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    change left (first (wedge ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))))+
      right (second (wedge ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))))=
      (4 : ℂ) • wedge ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
    simp only [first_wedge,second_wedge,rawFirst_pure,rawSecond_pure,left_pure,right_pure]
    rw [ExteriorSquareTensorDescent.wedge_swap (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d)]
    module
  have hh : (left (A := A) (B := B)).comp first+right.comp second=(4 : ℂ) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have he := LinearMap.congr_fun h (v 0 ⊗ₜ[ℂ] v 1)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
      LinearMap.id_apply,LinearMap.compAlternatingMap_apply,wedge_eta] using he
  exact LinearMap.congr_fun hh x

def forward : Total (A := A) (B := B) →ₗ[ℂ] First (A := A) (B := B) × Second (A := A) (B := B) :=
  first.prod second

def backward : First (A := A) (B := B) × Second (A := A) (B := B) →ₗ[ℂ] Total (A := A) (B := B) :=
  (4 : ℂ)⁻¹ • left.coprod right

def equivalence : Total (A := A) (B := B) ≃ₗ[ℂ] First (A := A) (B := B) × Second (A := A) (B := B) where
  toLinearMap := forward
  invFun := backward
  left_inv x := by
    change (4 : ℂ)⁻¹ • (left (first x)+right (second x))=x
    rw [reconstruct,smul_smul]
    norm_num
  right_inv x := by
    apply Prod.ext
    · change first ((4 : ℂ)⁻¹ • (left x.1+right x.2))=x.1
      rw [map_smul,map_add,first_left,first_right,add_zero,smul_smul]
      norm_num
    · change second ((4 : ℂ)⁻¹ • (left x.1+right x.2))=x.2
      rw [map_smul,map_add,second_left,second_right,zero_add,smul_smul]
      norm_num

end
end Math.ExteriorSquareCauchy
