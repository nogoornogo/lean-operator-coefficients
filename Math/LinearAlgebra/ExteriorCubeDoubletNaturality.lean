import Math.LinearAlgebra.ExteriorCubeDoublet
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-! Naturality of the symbolic cubic doublet contraction and insertion. -/
namespace Math.ExteriorCubeDoublet
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def tripleMap {V : Type*} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) :=
  TensorProduct.map f (TensorProduct.map f f)

def colorMap (f : A →ₗ[ℂ] A) := TensorProduct.map f (exteriorPower.map 2 f)

@[reducible] local instance : AddCommGroup (Target (A := A)) := inferInstance

theorem raw_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (he : ∀ s t, SU2DoubletDuality.epsilon (g s) (g t)=SU2DoubletDuality.epsilon s t) :
    (raw (A := A)).comp (tripleMap (TensorProduct.map f g))=
      (TensorProduct.map (colorMap f) g).comp raw := by
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro s
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro t
  apply TensorProduct.ext'
  intro c u
  change raw ((f a ⊗ₜ[ℂ] g s) ⊗ₜ[ℂ] ((f b ⊗ₜ[ℂ] g t) ⊗ₜ[ℂ] (f c ⊗ₜ[ℂ] g u)))=
    TensorProduct.map (colorMap f) g
      (raw ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] u))))
  rw [raw_pure,he,raw_pure,map_smul]
  simp only [TensorProduct.map_tmul,colorMap,← wedge_natural]

theorem contract_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (he : ∀ s t, SU2DoubletDuality.epsilon (g s) (g t)=SU2DoubletDuality.epsilon s t)
    (x : ⋀[ℂ]^3 (A ⊗[ℂ] B)) :
    contract (exteriorPower.map 3 (TensorProduct.map f g) x)=
      TensorProduct.map (colorMap f) g (contract x) := by
  have h : (contract (A := A)).comp (exteriorPower.map 3 (TensorProduct.map f g))=
      (TensorProduct.map (colorMap f) g).comp contract := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change contract (exteriorPower.map 3 (TensorProduct.map f g) (exteriorPower.ιMulti ℂ 3 v))=
      TensorProduct.map (colorMap f) g (contract (exteriorPower.ιMulti ℂ 3 v))
    rw [← cube_eta v,← cube_natural,contract_cube,contract_cube]
    have hr (x y z : A ⊗[ℂ] B) :=
      LinearMap.congr_fun (raw_natural f g he) (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z))
    simp only [LinearMap.comp_apply,tripleMap,TensorProduct.map_tmul] at hr
    simp only [hr,map_add,map_sub]
  exact LinearMap.congr_fun h x

theorem alternatingSection_natural (f : A →ₗ[ℂ] A) (x : ⋀[ℂ]^2 A) :
    alternatingSection (exteriorPower.map 2 f x)=
      TensorProduct.map f f (alternatingSection x) := by
  have h : (alternatingSection (A := A)).comp (exteriorPower.map 2 f)=
      (TensorProduct.map f f).comp alternatingSection := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change alternatingSection (exteriorPower.map 2 f (exteriorPower.ιMulti ℂ 2 v))=
      TensorProduct.map f f (alternatingSection (exteriorPower.ιMulti ℂ 2 v))
    rw [← wedge_eta v,← wedge_natural,alternatingSection_pure,alternatingSection_pure]
    simp only [map_sub,TensorProduct.map_tmul]
  exact LinearMap.congr_fun h x

def spinVolume : B ⊗[ℂ] B := e0 ⊗ₜ[ℂ] e1-e1 ⊗ₜ[ℂ] e0

theorem spinInsert_natural (g : B →ₗ[ℂ] B)
    (hv : TensorProduct.map g g spinVolume=spinVolume) (s : B) :
    spinInsert (g s)=tripleMap g (spinInsert s) := by
  have hh := congrArg (fun z => TensorProduct.assoc ℂ B B B (z ⊗ₜ[ℂ] g s)) hv
  simpa only [spinVolume,TensorProduct.sub_tmul,map_sub,TensorProduct.map_tmul,
    TensorProduct.assoc_tmul,spinInsert,LinearMap.comp_apply,TensorProduct.mk_apply,
    LinearEquiv.coe_coe,tripleMap] using hh.symm

theorem colorInsert_natural (f : A →ₗ[ℂ] A) (x : Source (V := A)) :
    TensorProduct.map LinearMap.id alternatingSection (colorMap f x)=
      tripleMap f (TensorProduct.map LinearMap.id alternatingSection x) := by
  have h : (TensorProduct.map LinearMap.id alternatingSection).comp (colorMap f)=
      (tripleMap f).comp (TensorProduct.map LinearMap.id alternatingSection) := by
    apply TensorProduct.ext'
    intro a y
    simp only [LinearMap.comp_apply,colorMap,tripleMap,TensorProduct.map_tmul,
      LinearMap.id_apply,alternatingSection_natural]
  exact LinearMap.congr_fun h x

theorem regroup_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (x : Triple A) (y : Triple B) :
    (regroup (A := A)).symm ((tripleMap f x) ⊗ₜ[ℂ] (tripleMap g y))=
      tripleMap (TensorProduct.map f g) (regroup.symm (x ⊗ₜ[ℂ] y)) := by
  have h : (regroup (A := A)).symm.toLinearMap.comp
      (TensorProduct.map (tripleMap f) (tripleMap g))=
      (tripleMap (TensorProduct.map f g)).comp regroup.symm.toLinearMap := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply TensorProduct.ext'
    intro b c
    apply TensorProduct.ext_threefold'
    intro s t u
    rfl
  exact LinearMap.congr_fun h (x ⊗ₜ[ℂ] y)

theorem spinVolume_invariant (g : B →ₗ[ℂ] B) (hd : LinearMap.det g=1) :
    TensorProduct.map g g spinVolume=spinVolume := by
  have ht : exteriorPower.map 2 g (wedge (e0 ⊗ₜ[ℂ] e1))=wedge (e0 ⊗ₜ[ℂ] e1) := by
    have hh := LinearMap.congr_fun
      (exteriorPower.map_top_eq_det_smul (Pi.basisFun ℂ (Fin 2)) g) (wedge (e0 ⊗ₜ[ℂ] e1))
    simpa only [hd,one_smul,LinearMap.id_apply] using hh
  have hh := alternatingSection_natural g (wedge (e0 ⊗ₜ[ℂ] e1))
  rw [ht,alternatingSection_pure] at hh
  exact hh.symm

theorem tensorCube_natural {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] V) (z : Triple V) :
    TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap
      (tripleMap f z)=exteriorPower.map 3 f
      (TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap z) := by
  have h : (TensorCubeMultilinear.fromMultilinear
      (exteriorPower.ιMulti ℂ 3).toMultilinearMap).comp (tripleMap f)=
      (exteriorPower.map 3 f).comp (TensorCubeMultilinear.fromMultilinear
        (exteriorPower.ιMulti ℂ 3).toMultilinearMap) := by
    apply TensorProduct.ext_threefold'
    intro a b c
    exact cube_natural f a b c
  exact LinearMap.congr_fun h z

theorem insert_natural (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (hv : TensorProduct.map g g spinVolume=spinVolume) (x : Target (A := A)) :
    insert (TensorProduct.map (colorMap f) g x)=
      exteriorPower.map 3 (TensorProduct.map f g) (insert x) := by
  have h : (insert (A := A)).comp (TensorProduct.map (colorMap f) g)=
      (exteriorPower.map 3 (TensorProduct.map f g)).comp insert := by
    apply TensorProduct.ext'
    intro x s
    change TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap
        (regroup.symm ((TensorProduct.map LinearMap.id alternatingSection (colorMap f x))
          ⊗ₜ[ℂ] spinInsert (g s)))=
      exteriorPower.map 3 (TensorProduct.map f g)
        (TensorCubeMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 3).toMultilinearMap
          (regroup.symm ((TensorProduct.map LinearMap.id alternatingSection x) ⊗ₜ[ℂ] spinInsert s)))
    rw [colorInsert_natural,spinInsert_natural g hv,regroup_natural,tensorCube_natural]
  exact LinearMap.congr_fun h x

end
end Math.ExteriorCubeDoublet
