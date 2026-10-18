import Math.LinearAlgebra.ExteriorFourthDoublet22
import Math.LinearAlgebra.ExteriorCubeDoubletNaturality

/-! The two quartic insertions retain an arbitrary color action and every
doublet transformation preserving its actual determinant tensor. -/
namespace Math.ExteriorFourthDoubletNaturality
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook ExteriorFourthKernels ExteriorFourthShuffle
open TensorFourthMultilinear ExteriorFourthDoublet ExteriorFourthDoublet22
open ExteriorFourthColumn (tensorMap)
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Target13 (A := A)) := inferInstance

theorem symmetricSection_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (x : Sym[ℂ]^2 V) :
    symmetricSection (SymmetricPower.map (ι := Fin 2) f x)=
      TensorProduct.map f f (symmetricSection x) := by
  have h : (symmetricSection (A := V)).comp (SymmetricPower.map (ι := Fin 2) f)=
      (TensorProduct.map f f).comp symmetricSection := by
    apply SymmetricPower.ext
    intro v
    rw [← sym_eta v]
    change symmetricSection (SymmetricPower.map (ι := Fin 2) f (sym (v 0 ⊗ₜ[ℂ] v 1)))=
      TensorProduct.map f f (symmetricSection (sym (v 0 ⊗ₜ[ℂ] v 1)))
    rw [← sym_natural, symmetricSection_pure, symmetricSection_pure]
    simp only [map_add, TensorProduct.map_tmul]
  exact LinearMap.congr_fun h x

theorem cubeSection_natural (f : A →ₗ[ℂ] A) (x : ⋀[ℂ]^3 A) :
    cubeSection (exteriorPower.map 3 f x)=
      ExteriorCubeDoublet.tripleMap f (cubeSection x) := by
  have h : (cubeSection (A := A)).comp (exteriorPower.map 3 f)=
      (ExteriorCubeDoublet.tripleMap f).comp cubeSection := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change cubeSection (exteriorPower.map 3 f (exteriorPower.ιMulti ℂ 3 v))=
      ExteriorCubeDoublet.tripleMap f (cubeSection (exteriorPower.ιMulti ℂ 3 v))
    rw [← cube_eta v, ← cube_natural, cubeSection_pure, cubeSection_pure]
    simp only [map_add, map_sub, ExteriorCubeDoublet.tripleMap, TensorProduct.map_tmul]
  exact LinearMap.congr_fun h x

theorem assoc_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (x : (V ⊗[ℂ] V) ⊗[ℂ] (V ⊗[ℂ] V)) :
    TensorProduct.assoc ℂ V V (V ⊗[ℂ] V)
      (TensorProduct.map (TensorProduct.map f f) (TensorProduct.map f f) x)=
      tensorMap f (TensorProduct.assoc ℂ V V (V ⊗[ℂ] V) x) := by
  have h : (TensorProduct.assoc ℂ V V (V ⊗[ℂ] V)).toLinearMap.comp
      (TensorProduct.map (TensorProduct.map f f) (TensorProduct.map f f))=
      (tensorMap f).comp (TensorProduct.assoc ℂ V V (V ⊗[ℂ] V)).toLinearMap := by
    ext a b c d
    rfl
  exact LinearMap.congr_fun h x

theorem spinInsert13_natural (g : B →ₗ[ℂ] B)
    (hv : TensorProduct.map g g (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0)=
      e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) (y : Sym[ℂ]^2 B) :
    spinInsert13 (SymmetricPower.map (ι := Fin 2) g y)=tensorMap g (spinInsert13 y) := by
  change TensorProduct.assoc ℂ B B (B ⊗[ℂ] B)
      ((e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) ⊗ₜ[ℂ] symmetricSection (SymmetricPower.map (ι := Fin 2) g y))=
    tensorMap g (TensorProduct.assoc ℂ B B (B ⊗[ℂ] B)
      ((e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) ⊗ₜ[ℂ] symmetricSection y))
  rw [symmetricSection_natural, ← assoc_natural, TensorProduct.map_tmul, hv]

def colorMap13 (f : A →ₗ[ℂ] A) := TensorProduct.map f (exteriorPower.map 3 f)

theorem colorInsert13_natural (f : A →ₗ[ℂ] A) (x : Source13 (A := A)) :
    TensorProduct.map LinearMap.id cubeSection (colorMap13 f x)=
      tensorMap f (TensorProduct.map LinearMap.id cubeSection x) := by
  have h : (TensorProduct.map LinearMap.id cubeSection).comp (colorMap13 f)=
      (tensorMap f).comp (TensorProduct.map LinearMap.id cubeSection) := by
    apply TensorProduct.ext'
    intro a y
    simp only [LinearMap.comp_apply, colorMap13, TensorProduct.map_tmul,
      LinearMap.id_apply, cubeSection_natural, tensorMap, ExteriorCubeDoublet.tripleMap]
  exact LinearMap.congr_fun h x

theorem regroup_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (x : Tensor (V := A)) (y : Tensor (V := B)) :
    ExteriorFourthColumn.regroup.symm ((tensorMap f x) ⊗ₜ[ℂ] (tensorMap g y))=
      tensorMap (TensorProduct.map f g) (ExteriorFourthColumn.regroup.symm (x ⊗ₜ[ℂ] y)) := by
  have h : (ExteriorFourthColumn.regroup (A := A) (B := B)).symm.toLinearMap.comp
      (TensorProduct.map (tensorMap f) (tensorMap g))=
      (tensorMap (TensorProduct.map f g)).comp ExteriorFourthColumn.regroup.symm.toLinearMap := by
    ext a b c d s t u v
    rfl
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)

theorem tensorFourth_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (x : Tensor (V := V)) :
    fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap (tensorMap f x)=
      exteriorPower.map 4 f (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap x) := by
  have h : (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap).comp (tensorMap f)=
      (exteriorPower.map 4 f).comp (fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply TensorProduct.ext
    apply LinearMap.ext
    intro b
    apply TensorProduct.ext'
    intro c d
    change exteriorPower.ιMulti ℂ 4 ![f a,f b,f c,f d]=
      exteriorPower.map 4 f (exteriorPower.ιMulti ℂ 4 ![a,b,c,d])
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    ext i
    fin_cases i <;> rfl
  exact LinearMap.congr_fun h x

theorem insert13_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (hv : TensorProduct.map g g (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0)=
      e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) (x : Target13 (A := A)) :
    insert13 (TensorProduct.map (colorMap13 f) (SymmetricPower.map (ι := Fin 2) g) x)=
      exteriorPower.map 4 (TensorProduct.map f g) (insert13 x) := by
  have h : (insert13 (A := A)).comp
      (TensorProduct.map (colorMap13 f) (SymmetricPower.map (ι := Fin 2) g))=
      (exteriorPower.map 4 (TensorProduct.map f g)).comp insert13 := by
    apply TensorProduct.ext'
    intro x y
    change fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap
      (ExteriorFourthColumn.regroup.symm
        (TensorProduct.map LinearMap.id cubeSection (colorMap13 f x) ⊗ₜ[ℂ]
          spinInsert13 (SymmetricPower.map (ι := Fin 2) g y)))=_
    rw [colorInsert13_natural, spinInsert13_natural g hv, regroup_natural, tensorFourth_natural]
    rfl
  exact LinearMap.congr_fun h x

theorem spinVolume22_natural (g : B →ₗ[ℂ] B)
    (hv : TensorProduct.map g g (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0)=
      e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) : tensorMap g spinVolume22=spinVolume22 := by
  have h : (middleSwap).comp (tensorMap g)=(tensorMap g).comp middleSwap := by
    ext s t u v
    rfl
  have hc (z : Tensor (V := B)) : tensorMap g (middleSwap z)=middleSwap (tensorMap g z) :=
    (LinearMap.congr_fun h z).symm
  rw [spinVolume22, hc, ← assoc_natural, TensorProduct.map_tmul, hv]

theorem colorInsert22_natural (f : A →ₗ[ℂ] A) (x : Source22 (A := A)) :
    colorInsert22 (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) x)=
      tensorMap f (colorInsert22 x) := by
  have h : (TensorProduct.map alternatingSection alternatingSection).comp
      (TensorProduct.map (exteriorPower.map 2 f) (exteriorPower.map 2 f))=
      (TensorProduct.map (TensorProduct.map f f) (TensorProduct.map f f)).comp
        (TensorProduct.map alternatingSection alternatingSection) := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
      ExteriorCubeDoublet.alternatingSection_natural]
  change TensorProduct.assoc ℂ A A (A ⊗[ℂ] A)
    (TensorProduct.map alternatingSection alternatingSection
      (symmetricSection (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) x)))=_
  rw [symmetricSection_natural]
  have hx := LinearMap.congr_fun h (symmetricSection x)
  change TensorProduct.map alternatingSection alternatingSection
      (TensorProduct.map (exteriorPower.map 2 f) (exteriorPower.map 2 f) (symmetricSection x))=_ at hx
  simp only [LinearMap.comp_apply] at hx
  rw [hx, assoc_natural]
  rfl

theorem insert22_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (hv : TensorProduct.map g g (e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0)=
      e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0) (x : Source22 (A := A)) :
    insert22 (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) x)=
      exteriorPower.map 4 (TensorProduct.map f g) (insert22 x) := by
  change fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap
    (ExteriorFourthColumn.regroup.symm
      (colorInsert22 (SymmetricPower.map (ι := Fin 2) (exteriorPower.map 2 f) x) ⊗ₜ[ℂ] spinVolume22))=_
  rw [colorInsert22_natural]
  calc
    _=fromMultilinear (exteriorPower.ιMulti ℂ 4).toMultilinearMap
        (ExteriorFourthColumn.regroup.symm
          (tensorMap f (colorInsert22 x) ⊗ₜ[ℂ] tensorMap g spinVolume22)) := by
            rw [spinVolume22_natural g hv]
    _=_ := by
      rw [regroup_natural, tensorFourth_natural]
      rfl

end
end Math.ExteriorFourthDoubletNaturality
