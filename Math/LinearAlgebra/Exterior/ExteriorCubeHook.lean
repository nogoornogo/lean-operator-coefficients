import Math.LinearAlgebra.Tensor.TensorSquareQuotients
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! The universal degree-three hook kernel, by multiplication and its
coproduct. All identities hold on arbitrary vectors, without a basis. -/
namespace Math.ExteriorCubeHook
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
abbrev Source := V ⊗[ℂ] ⋀[ℂ]^2 V
abbrev Cube := ⋀[ℂ]^3 V

@[reducible] local instance : AddCommGroup (Source (V := V)) := inferInstance

def cube (a b c : V) : Cube (V := V) := exteriorPower.ιMulti ℂ 3 ![a,b,c]

theorem cube_swap01 (a b c : V) : cube b a c = -cube a b c := by
  have he : (![a,b,c] : Fin 3 → V) ∘ Equiv.swap 0 1=![b,a,c] := by
    ext i
    fin_cases i <;> rfl
  simpa only [he,cube] using (exteriorPower.ιMulti ℂ 3).map_swap ![a,b,c] (by decide : (0 : Fin 3)≠1)

theorem cube_swap12 (a b c : V) : cube a c b = -cube a b c := by
  have he : (![a,b,c] : Fin 3 → V) ∘ Equiv.swap 1 2=![a,c,b] := by
    ext i
    fin_cases i <;> rfl
  simpa only [he,cube] using (exteriorPower.ιMulti ℂ 3).map_swap ![a,b,c] (by decide : (1 : Fin 3)≠2)

theorem cube_cycle (a b c : V) : cube c a b=cube a b c := by
  rw [cube_swap01 a c b,cube_swap12 a b c,neg_neg]

def multiply : Source (V := V) →ₗ[ℂ] Cube (V := V) :=
  TensorProduct.lift ((exteriorPower.wedge ℂ V 1 2).comp
    (exteriorPower.oneEquiv ℂ V).symm.toLinearMap)

@[simp] theorem multiply_pure (a b c : V) : multiply (a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c))=cube a b c := by
  apply Subtype.ext
  change (exteriorPower.wedge ℂ V 1 2 ((exteriorPower.oneEquiv ℂ V).symm a)
    (exteriorPower.ιMulti ℂ 2 ![b,c])).val=(exteriorPower.ιMulti ℂ 3 ![a,b,c]).val
  simp [exteriorPower.wedge,exteriorPower.oneEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_succ_apply]

theorem wedge_self (a : V) : wedge (a ⊗ₜ[ℂ] a)=0 :=
  (exteriorPower.ιMulti ℂ 2).map_eq_zero_of_eq ![a,a] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2)≠1)

def raw : MultilinearMap ℂ (fun _ : Fin 3 => V) (Source (V := V)) :=
  MultilinearMap.mk' (fun v =>
    v 0 ⊗ₜ[ℂ] wedge (v 1 ⊗ₜ[ℂ] v 2)-v 1 ⊗ₜ[ℂ] wedge (v 0 ⊗ₜ[ℂ] v 2)+
      v 2 ⊗ₜ[ℂ] wedge (v 0 ⊗ₜ[ℂ] v 1))
    (by
      intro v i x y
      fin_cases i <;> simp [Function.update,TensorProduct.add_tmul,TensorProduct.tmul_add,
        map_add] <;> module)
    (by
      intro v i z x
      fin_cases i <;> simp [Function.update,TensorProduct.smul_tmul,TensorProduct.tmul_smul,
        map_smul,smul_sub,smul_add])

theorem raw_repeat01 (a b : V) : raw ![a,a,b]=0 := by
  change a ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b)-a ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b)+b ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] a)=0
  rw [sub_self,wedge_self,TensorProduct.tmul_zero,add_zero]

theorem raw_repeat02 (a b : V) : raw ![a,b,a]=0 := by
  change a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] a)-b ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] a)+a ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b)=0
  rw [wedge_self,TensorProduct.tmul_zero,sub_zero,
    ExteriorSquareTensorDescent.wedge_swap a b,TensorProduct.tmul_neg,neg_add_cancel]

theorem raw_repeat12 (a b : V) : raw ![a,b,b]=0 := by
  change a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] b)-b ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b)+b ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b)=0
  rw [wedge_self,TensorProduct.tmul_zero,zero_sub,neg_add_cancel]

def alternating : V [⋀^Fin 3]→ₗ[ℂ] Source (V := V) where
  toMultilinearMap := raw
  map_eq_zero_of_eq' v i j hij hne := by
    change raw ![v 0,v 1,v 2]=0
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0=v 1 at hij
      rw [hij]
      exact raw_repeat01 (v 1) (v 2)
    · change v 0=v 2 at hij
      rw [hij]
      exact raw_repeat02 (v 2) (v 1)
    · change v 1=v 0 at hij
      rw [hij]
      exact raw_repeat01 (v 0) (v 2)
    · exact (hne rfl).elim
    · change v 1=v 2 at hij
      rw [hij]
      exact raw_repeat12 (v 0) (v 2)
    · change v 2=v 0 at hij
      rw [hij]
      exact raw_repeat02 (v 0) (v 1)
    · change v 2=v 1 at hij
      rw [hij]
      exact raw_repeat12 (v 0) (v 1)
    · exact (hne rfl).elim

def coproduct : Cube (V := V) →ₗ[ℂ] Source (V := V) := exteriorPower.alternatingMapLinearEquiv alternating

@[simp] theorem coproduct_pure (a b c : V) : coproduct (cube a b c)=
    a ⊗ₜ[ℂ] wedge (b ⊗ₜ[ℂ] c)-b ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] c)+c ⊗ₜ[ℂ] wedge (a ⊗ₜ[ℂ] b) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem multiply_coproduct (x : Cube (V := V)) : multiply (coproduct x)=(3 : ℂ) • x := by
  have h : (multiply (V := V)).comp coproduct=(3 : ℂ) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hv : (![v 0,v 1,v 2] : Fin 3 → V)=v := by ext i; fin_cases i <;> rfl
    change multiply (coproduct (exteriorPower.ιMulti ℂ 3 v))=(3 : ℂ) • exteriorPower.ιMulti ℂ 3 v
    rw [← hv]
    change multiply (coproduct (cube _ _ _))=(3 : ℂ) • cube _ _ _
    rw [coproduct_pure,map_add,map_sub,multiply_pure,multiply_pure,multiply_pure,
      cube_swap01 (v 0) (v 1) (v 2),cube_cycle (v 0) (v 1) (v 2)]
    module
  exact LinearMap.congr_fun h x

abbrev Hook := LinearMap.ker (multiply (V := V))

def project : Source (V := V) →ₗ[ℂ] Hook (V := V) :=
  ((LinearMap.id : Source (V := V) →ₗ[ℂ] Source (V := V))-
    (3 : ℂ)⁻¹ • (coproduct (V := V)).comp multiply).codRestrict _ (by
    intro x
    change multiply (x-(3 : ℂ)⁻¹ • coproduct (multiply x))=0
    rw [map_sub,map_smul,multiply_coproduct,smul_smul]
    norm_num)

theorem project_hook (x : Hook (V := V)) : project x.val=x := by
  apply Subtype.ext
  change x.val-(3 : ℂ)⁻¹ • coproduct (multiply x.val)=x.val
  rw [show multiply x.val=0 from x.property,map_zero,smul_zero,sub_zero]

theorem cube_eta (v : Fin 3 → V) : cube (v 0) (v 1) (v 2)=exteriorPower.ιMulti ℂ 3 v := by
  unfold cube
  congr 1
  ext i
  fin_cases i <;> rfl

theorem cube_natural (f : V →ₗ[ℂ] V) (a b c : V) :
    cube (f a) (f b) (f c)=exteriorPower.map 3 f (cube a b c) := by
  unfold cube
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem wedge_natural (f : V →ₗ[ℂ] V) (a b : V) :
    wedge (f a ⊗ₜ[ℂ] f b)=exteriorPower.map 2 f (wedge (a ⊗ₜ[ℂ] b)) := by
  rw [ExteriorSquareTensorDescent.wedge_tmul,ExteriorSquareTensorDescent.wedge_tmul,
    exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply_natural (f : V →ₗ[ℂ] V) (a : V) (x : ⋀[ℂ]^2 V) :
    multiply (f a ⊗ₜ[ℂ] exteriorPower.map 2 f x)=exteriorPower.map 3 f (multiply (a ⊗ₜ[ℂ] x)) := by
  have h : (multiply (V := V)).comp ((TensorProduct.mk ℂ V (⋀[ℂ]^2 V) (f a)).comp
      (exteriorPower.map 2 f))=
      (exteriorPower.map 3 f).comp (multiply.comp (TensorProduct.mk ℂ V (⋀[ℂ]^2 V) a)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change multiply (f a ⊗ₜ[ℂ] exteriorPower.map 2 f (exteriorPower.ιMulti ℂ 2 v))=
      exteriorPower.map 3 f (multiply (a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v))
    rw [← wedge_eta v,← wedge_natural,multiply_pure,multiply_pure,cube_natural]
  exact LinearMap.congr_fun h x

theorem coproduct_natural (f : V →ₗ[ℂ] V) (x : Cube (V := V)) :
    coproduct (exteriorPower.map 3 f x)=TensorProduct.map f (exteriorPower.map 2 f) (coproduct x) := by
  have h : (coproduct (V := V)).comp (exteriorPower.map 3 f)=
      (TensorProduct.map f (exteriorPower.map 2 f)).comp coproduct := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change coproduct (exteriorPower.map 3 f (exteriorPower.ιMulti ℂ 3 v))=
      TensorProduct.map f (exteriorPower.map 2 f) (coproduct (exteriorPower.ιMulti ℂ 3 v))
    rw [← cube_eta v,← cube_natural,coproduct_pure,coproduct_pure]
    simp only [map_add,map_sub,TensorProduct.map_tmul,← wedge_natural]
  exact LinearMap.congr_fun h x

theorem project_coproduct (x : Cube (V := V)) : project (coproduct x)=0 := by
  apply Subtype.ext
  change coproduct x-(3 : ℂ)⁻¹ • coproduct (multiply (coproduct x))=0
  rw [multiply_coproduct,map_smul,smul_smul]
  norm_num

def split : Source (V := V) ≃ₗ[ℂ] Cube (V := V) × Hook (V := V) where
  toLinearMap := ((3 : ℂ)⁻¹ • multiply).prod project
  invFun x := coproduct x.1+x.2.val
  left_inv x := by
    change coproduct ((3 : ℂ)⁻¹ • multiply x)+(x-(3 : ℂ)⁻¹ • coproduct (multiply x))=x
    rw [map_smul]
    module
  right_inv x := by
    apply Prod.ext
    · change (3 : ℂ)⁻¹ • multiply (coproduct x.1+x.2.val)=x.1
      rw [map_add,multiply_coproduct,show multiply x.2.val=0 from x.2.property,
        add_zero,smul_smul]
      norm_num
    · change project (coproduct x.1+x.2.val)=x.2
      rw [map_add,project_coproduct,project_hook,zero_add]

end
end Math.ExteriorCubeHook
