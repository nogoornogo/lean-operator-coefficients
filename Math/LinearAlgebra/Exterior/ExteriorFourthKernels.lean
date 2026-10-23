import Math.LinearAlgebra.Exterior.ExteriorCubeHook
import Math.LinearAlgebra.Constructions.SectionKernel

/-! The two actual quartic exterior multiplication quotients. Their sections
come from a universal alternator, not representation coefficient evaluation. -/
namespace Math.ExteriorFourthKernels
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]

abbrev Fourth := ⋀[ℂ]^4 A
abbrev Source13 := A ⊗[ℂ] ⋀[ℂ]^3 A
abbrev Source22 := Sym[ℂ]^2 (⋀[ℂ]^2 A)

@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

def fourth (a b c d : A) : Fourth (A := A) := exteriorPower.ιMulti ℂ 4 ![a,b,c,d]

theorem fourth_eta (v : Fin 4 → A) :
    fourth (v 0) (v 1) (v 2) (v 3)=exteriorPower.ιMulti ℂ 4 v := by
  unfold fourth
  congr 1
  ext i
  fin_cases i <;> rfl

def multiply13 : Source13 (A := A) →ₗ[ℂ] Fourth (A := A) :=
  TensorProduct.lift ((exteriorPower.wedge ℂ A 1 3).comp
    (exteriorPower.oneEquiv ℂ A).symm.toLinearMap)

@[simp] theorem multiply13_pure (a b c d : A) :
    multiply13 (a ⊗ₜ[ℂ] ExteriorCubeHook.cube b c d)=fourth a b c d := by
  apply Subtype.ext
  simp [multiply13, ExteriorCubeHook.cube, fourth, exteriorPower.wedge,
    exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_succ_apply]

def wedge22 : ((⋀[ℂ]^2 A) ⊗[ℂ] (⋀[ℂ]^2 A)) →ₗ[ℂ] Fourth (A := A) :=
  TensorProduct.lift (exteriorPower.wedge ℂ A 2 2)

@[simp] theorem wedge22_pure (a b c d : A) :
    wedge22 (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d))=fourth a b c d := by
  apply Subtype.ext
  simp [wedge22, ExteriorSquareTensorDescent.wedge_tmul, fourth, exteriorPower.wedge,
    ExteriorAlgebra.ιMulti_succ_apply, mul_assoc]

theorem wedge22_swap (x y : ⋀[ℂ]^2 A) :
    wedge22 (y ⊗ₜ[ℂ] x)=wedge22 (x ⊗ₜ[ℂ] y) := by
  have h : (wedge22 (A := A)).comp (TensorProduct.comm ℂ _ _).toLinearMap=wedge22 := by
    apply TensorProduct.ext'
    intro x y
    have hxy : ((wedge22 (A := A)).comp (TensorProduct.mk ℂ _ _ y)) =
        ((wedge22 (A := A)).comp ((TensorProduct.mk ℂ _ _).flip y)) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      have hy : ((TensorProduct.lift (exteriorPower.wedge ℂ A 2 2)).comp
          ((TensorProduct.mk ℂ _ _).flip (exteriorPower.ιMulti ℂ 2 v))) =
          ((TensorProduct.lift (exteriorPower.wedge ℂ A 2 2)).comp
          (TensorProduct.mk ℂ _ _ (exteriorPower.ιMulti ℂ 2 v))) := by
        apply exteriorPower.linearMap_ext
        apply AlternatingMap.ext
        intro w
        apply Subtype.ext
        change ExteriorAlgebra.ιMulti ℂ 2 w * ExteriorAlgebra.ιMulti ℂ 2 v =
          ExteriorAlgebra.ιMulti ℂ 2 v * ExteriorAlgebra.ιMulti ℂ 2 w
        simpa only [pow_mul, neg_one_sq, one_pow, one_smul] using
          (ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm ℂ w v)
      exact LinearMap.congr_fun hy y
    exact LinearMap.congr_fun hxy x
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)

def multiply22 : Source22 (A := A) →ₗ[ℂ] Fourth (A := A) :=
  symmetricLift wedge22 wedge22_swap

@[simp] theorem multiply22_pure (a b c d : A) :
    multiply22 (sym (wedge (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] wedge (c ⊗ₜ[ℂ] d)))=fourth a b c d := by
  rw [multiply22, symmetricLift_pure, wedge22_pure]

theorem cube_add_left (a b c d : A) :
    ExteriorCubeHook.cube (a+b) c d=ExteriorCubeHook.cube a c d+ExteriorCubeHook.cube b c d := by
  simpa only [ExteriorCubeHook.cube] using
    (exteriorPower.ιMulti ℂ 3).map_vecCons_add ![c,d] a b

theorem cube_smul_left (z : ℂ) (a b c : A) :
    ExteriorCubeHook.cube (z • a) b c=z • ExteriorCubeHook.cube a b c := by
  simpa only [ExteriorCubeHook.cube] using
    (exteriorPower.ιMulti ℂ 3).map_vecCons_smul ![b,c] z a

theorem cube_add_middle (a b c d : A) :
    ExteriorCubeHook.cube a (b+c) d=ExteriorCubeHook.cube a b d+ExteriorCubeHook.cube a c d := by
  rw [ExteriorCubeHook.cube_swap01, cube_add_left,
    ExteriorCubeHook.cube_swap01 b a d, ExteriorCubeHook.cube_swap01 c a d]
  module

theorem cube_smul_middle (z : ℂ) (a b c : A) :
    ExteriorCubeHook.cube a (z • b) c=z • ExteriorCubeHook.cube a b c := by
  rw [ExteriorCubeHook.cube_swap01, cube_smul_left, ExteriorCubeHook.cube_swap01 b a c]
  module

theorem cube_add_right (a b c d : A) :
    ExteriorCubeHook.cube a b (c+d)=ExteriorCubeHook.cube a b c+ExteriorCubeHook.cube a b d := by
  rw [← ExteriorCubeHook.cube_cycle a b (c+d), cube_add_left,
    ExteriorCubeHook.cube_cycle a b c, ExteriorCubeHook.cube_cycle a b d]

theorem cube_smul_right (z : ℂ) (a b c : A) :
    ExteriorCubeHook.cube a b (z • c)=z • ExteriorCubeHook.cube a b c := by
  rw [← ExteriorCubeHook.cube_cycle a b (z • c), cube_smul_left,
    ExteriorCubeHook.cube_cycle a b c]

def raw13 : MultilinearMap ℂ (fun _ : Fin 4 => A) (Source13 (A := A)) :=
  MultilinearMap.mk' (fun v => v 0 ⊗ₜ[ℂ] ExteriorCubeHook.cube (v 1) (v 2) (v 3))
    (by
      intro v i x y
      fin_cases i <;> simp [Function.update, cube_add_left, cube_add_middle, cube_add_right,
        TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by
      intro v i z x
      fin_cases i <;> simp [Function.update, cube_smul_left, cube_smul_middle, cube_smul_right,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul])

def raw22 : MultilinearMap ℂ (fun _ : Fin 4 => A) (Source22 (A := A)) :=
  MultilinearMap.mk' (fun v => sym (wedge (v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ]
      wedge (v 2 ⊗ₜ[ℂ] v 3)))
    (by
      intro v i x y
      fin_cases i <;> simp [Function.update, TensorProduct.add_tmul,
        TensorProduct.tmul_add, map_add])
    (by
      intro v i z x
      fin_cases i <;> simp [Function.update, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, map_smul])

def coproduct13 : Fourth (A := A) →ₗ[ℂ] Source13 (A := A) :=
  exteriorPower.alternatingMapLinearEquiv raw13.alternatization

def coproduct22 : Fourth (A := A) →ₗ[ℂ] Source22 (A := A) :=
  exteriorPower.alternatingMapLinearEquiv raw22.alternatization

theorem multiply13_raw :
    (multiply13 (A := A)).compMultilinearMap raw13=(exteriorPower.ιMulti ℂ 4).toMultilinearMap := by
  apply MultilinearMap.ext
  intro v
  exact (multiply13_pure _ _ _ _).trans (fourth_eta v)

theorem multiply22_raw :
    (multiply22 (A := A)).compMultilinearMap raw22=(exteriorPower.ιMulti ℂ 4).toMultilinearMap := by
  apply MultilinearMap.ext
  intro v
  exact (multiply22_pure _ _ _ _).trans (fourth_eta v)

theorem multiply13_coproduct (x : Fourth (A := A)) :
    multiply13 (coproduct13 x)=(24 : ℂ) • x := by
  have ha : (multiply13 (A := A)).compAlternatingMap raw13.alternatization =
      (24 : ℂ) • exteriorPower.ιMulti ℂ 4 := by
    rw [← LinearMap.compMultilinearMap_alternatization, multiply13_raw,
      AlternatingMap.coe_alternatization]
    norm_num
    apply AlternatingMap.ext
    intro v
    exact (Nat.cast_smul_eq_nsmul ℂ 24 (exteriorPower.ιMulti ℂ 4 v)).symm
  have h : (multiply13 (A := A)).comp coproduct13=(24 : ℂ) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change multiply13 (coproduct13 (exteriorPower.ιMulti ℂ 4 v)) =
      (24 : ℂ) • exteriorPower.ιMulti ℂ 4 v
    rw [coproduct13, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact DFunLike.congr_fun ha v
  exact LinearMap.congr_fun h x

theorem multiply22_coproduct (x : Fourth (A := A)) :
    multiply22 (coproduct22 x)=(24 : ℂ) • x := by
  have ha : (multiply22 (A := A)).compAlternatingMap raw22.alternatization =
      (24 : ℂ) • exteriorPower.ιMulti ℂ 4 := by
    rw [← LinearMap.compMultilinearMap_alternatization, multiply22_raw,
      AlternatingMap.coe_alternatization]
    norm_num
    apply AlternatingMap.ext
    intro v
    exact (Nat.cast_smul_eq_nsmul ℂ 24 (exteriorPower.ιMulti ℂ 4 v)).symm
  have h : (multiply22 (A := A)).comp coproduct22=(24 : ℂ) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change multiply22 (coproduct22 (exteriorPower.ιMulti ℂ 4 v)) =
      (24 : ℂ) • exteriorPower.ιMulti ℂ 4 v
    rw [coproduct22, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact DFunLike.congr_fun ha v
  exact LinearMap.congr_fun h x

abbrev K211 := LinearMap.ker (multiply13 (A := A))
abbrev K22 := LinearMap.ker (multiply22 (A := A))

def section13 : Fourth (A := A) →ₗ[ℂ] Source13 (A := A) :=
  (24 : ℂ)⁻¹ • coproduct13

def section22 : Fourth (A := A) →ₗ[ℂ] Source22 (A := A) :=
  (24 : ℂ)⁻¹ • coproduct22

theorem multiply13_section (x : Fourth (A := A)) : multiply13 (section13 x)=x := by
  simp only [section13, LinearMap.smul_apply, map_smul, multiply13_coproduct, smul_smul]
  norm_num

theorem multiply22_section (x : Fourth (A := A)) : multiply22 (section22 x)=x := by
  simp only [section22, LinearMap.smul_apply, map_smul, multiply22_coproduct, smul_smul]
  norm_num

def project211 : Source13 (A := A) →ₗ[ℂ] K211 (A := A) :=
  SectionKernel.project multiply13 section13 multiply13_section

def project22 : Source22 (A := A) →ₗ[ℂ] K22 (A := A) :=
  SectionKernel.project multiply22 section22 multiply22_section

theorem project211_kernel (x : K211 (A := A)) : project211 x.val=x :=
  SectionKernel.project_kernel _ _ _ x

theorem project22_kernel (x : K22 (A := A)) : project22 x.val=x :=
  SectionKernel.project_kernel _ _ _ x

theorem project211_section (x : Fourth (A := A)) : project211 (section13 x)=0 :=
  SectionKernel.project_section _ _ _ x

theorem project22_section (x : Fourth (A := A)) : project22 (section22 x)=0 :=
  SectionKernel.project_section _ _ _ x

def split13 : Source13 (A := A) ≃ₗ[ℂ] Fourth (A := A) × K211 (A := A) :=
  SectionKernel.equivalence multiply13 section13 multiply13_section

def split22 : Source22 (A := A) ≃ₗ[ℂ] Fourth (A := A) × K22 (A := A) :=
  SectionKernel.equivalence multiply22 section22 multiply22_section

theorem multiply13_natural (f : A →ₗ[ℂ] A) (a : A) (x : ⋀[ℂ]^3 A) :
    multiply13 (f a ⊗ₜ[ℂ] exteriorPower.map 3 f x)=
      exteriorPower.map 4 f (multiply13 (a ⊗ₜ[ℂ] x)) := by
  apply Subtype.ext
  simp [multiply13, exteriorPower.wedge, exteriorPower.oneEquiv_symm_apply]

theorem wedge22_natural (f : A →ₗ[ℂ] A) (x y : ⋀[ℂ]^2 A) :
    wedge22 (exteriorPower.map 2 f x ⊗ₜ[ℂ] exteriorPower.map 2 f y)=
      exteriorPower.map 4 f (wedge22 (x ⊗ₜ[ℂ] y)) := by
  apply Subtype.ext
  simp [wedge22, exteriorPower.wedge]

theorem sym_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (x y : V) :
    sym (f x ⊗ₜ[ℂ] f y)=SymmetricPower.map (ι := Fin 2) f (sym (x ⊗ₜ[ℂ] y)) := by
  rw [sym_tmul, sym_tmul, SymmetricPower.map_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem multiply22_natural (f : A →ₗ[ℂ] A) (x : Source22 (A := A)) :
    multiply22 (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) x)=
      exteriorPower.map 4 f (multiply22 x) := by
  have h : (multiply22 (A := A)).comp (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f))=
      (exteriorPower.map 4 f).comp multiply22 := by
    apply SymmetricPower.ext
    intro v
    change multiply22 (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f)
      (sym (v 0 ⊗ₜ[ℂ] v 1)))=exteriorPower.map 4 f (multiply22 (sym (v 0 ⊗ₜ[ℂ] v 1)))
    rw [← sym_natural, multiply22, symmetricLift_pure, symmetricLift_pure]
    exact wedge22_natural f (v 0) (v 1)
  exact LinearMap.congr_fun h x

theorem raw13_natural (f : A →ₗ[ℂ] A) :
    (raw13 (A := A)).compLinearMap (fun _ => f)=
      (TensorProduct.map f (exteriorPower.map 3 f)).compMultilinearMap raw13 := by
  apply MultilinearMap.ext
  intro v
  change f (v 0) ⊗ₜ[ℂ] ExteriorCubeHook.cube (f (v 1)) (f (v 2)) (f (v 3)) =
    f (v 0) ⊗ₜ[ℂ] exteriorPower.map 3 f (ExteriorCubeHook.cube (v 1) (v 2) (v 3))
  rw [ExteriorCubeHook.cube_natural]

theorem raw22_natural (f : A →ₗ[ℂ] A) :
    (raw22 (A := A)).compLinearMap (fun _ => f)=
      (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f)).compMultilinearMap raw22 := by
  apply MultilinearMap.ext
  intro v
  change sym (wedge (f (v 0) ⊗ₜ[ℂ] f (v 1)) ⊗ₜ[ℂ] wedge (f (v 2) ⊗ₜ[ℂ] f (v 3))) =
    SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f)
      (sym (wedge (v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] wedge (v 2 ⊗ₜ[ℂ] v 3)))
  rw [ExteriorCubeHook.wedge_natural, ExteriorCubeHook.wedge_natural, sym_natural]

theorem coproduct13_natural (f : A →ₗ[ℂ] A) (x : Fourth (A := A)) :
    coproduct13 (exteriorPower.map 4 f x)=
      TensorProduct.map f (exteriorPower.map 3 f) (coproduct13 x) := by
  have ha := congrArg MultilinearMap.alternatization (raw13_natural f)
  rw [MultilinearMap.alternatization_compLinearMap,
    LinearMap.compMultilinearMap_alternatization] at ha
  have h : (coproduct13 (A := A)).comp (exteriorPower.map 4 f)=
      (TensorProduct.map f (exteriorPower.map 3 f)).comp coproduct13 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change coproduct13 (exteriorPower.map 4 f (exteriorPower.ιMulti ℂ 4 v))=
      TensorProduct.map f (exteriorPower.map 3 f) (coproduct13 (exteriorPower.ιMulti ℂ 4 v))
    rw [exteriorPower.map_apply_ιMulti, coproduct13,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact DFunLike.congr_fun ha v
  exact LinearMap.congr_fun h x

theorem coproduct22_natural (f : A →ₗ[ℂ] A) (x : Fourth (A := A)) :
    coproduct22 (exteriorPower.map 4 f x)=
      SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) (coproduct22 x) := by
  have ha := congrArg MultilinearMap.alternatization (raw22_natural f)
  rw [MultilinearMap.alternatization_compLinearMap,
    LinearMap.compMultilinearMap_alternatization] at ha
  have h : (coproduct22 (A := A)).comp (exteriorPower.map 4 f)=
      (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f)).comp coproduct22 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change coproduct22 (exteriorPower.map 4 f (exteriorPower.ιMulti ℂ 4 v))=
      SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) (coproduct22 (exteriorPower.ιMulti ℂ 4 v))
    rw [exteriorPower.map_apply_ιMulti, coproduct22,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact DFunLike.congr_fun ha v
  exact LinearMap.congr_fun h x

end
end Math.ExteriorFourthKernels
