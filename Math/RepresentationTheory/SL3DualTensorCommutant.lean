import Math.RepresentationTheory.SL3TensorCommutant

/-! The same actual permutation commutant for contragredient color powers.
Inverse transpose transports the action; no self-duality of color is asserted. -/
namespace Math.SL3DualTensorCommutant
set_option autoImplicit false
noncomputable section
open Representation SL3ColorPlanes SL3CompactComparison
open scoped TensorProduct

def inverseTranspose : Group →* Group where
  toFun g := ⟨g⁻¹.val.transpose,by rw [Matrix.det_transpose]; exact g⁻¹.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change ((g*h)⁻¹).val.transpose = g⁻¹.val.transpose * h⁻¹.val.transpose
    rw [mul_inv_rev]
    exact Matrix.transpose_mul _ _

theorem involution (g : Group) : inverseTranspose (inverseTranspose g) = g := by
  apply Subtype.ext
  change ((inverseTranspose g)⁻¹).val.transpose = g.val
  rw [← map_inv inverseTranspose]
  change (g⁻¹⁻¹).val.transpose.transpose = g.val
  simp

def dualCoordinates : (Module.Dual ℂ Vector) ≃ₗ[ℂ] Vector :=
  (Pi.basisFun ℂ (Fin 3)).dualBasis.equivFun

theorem dualCoordinates_apply (f : Module.Dual ℂ Vector) (i : Fin 3) :
    dualCoordinates f i = f (Pi.single i 1) := by
  simp [dualCoordinates,Pi.basisFun_apply]

def dualEquivalence : Representation.Equiv standard.dual
    (standard.comp inverseTranspose) where
  toLinearEquiv := dualCoordinates
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    funext i
    change dualCoordinates (standard.dual g f) i =
      standard (inverseTranspose g) (dualCoordinates f) i
    rw [dualCoordinates_apply]
    change f (g⁻¹.val.mulVec (Pi.single i 1)) =
      (g⁻¹.val.transpose).mulVec (dualCoordinates f) i
    have he := congrArg f ((Pi.basisFun ℂ (Fin 3)).sum_repr (fun j => g⁻¹.val j i))
    simp only [map_sum,map_smul,Pi.basisFun_repr,smul_eq_mul] at he
    have hv : g⁻¹.val.mulVec (Pi.single i 1) = (fun j => g⁻¹.val j i) := by
      funext j
      simp [Matrix.mulVec,dotProduct,Pi.single_apply]
    rw [hv]
    simpa only [Pi.basisFun_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      dualCoordinates_apply] using he.symm

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

def powerCoordinates (n : ℕ) :
    (⨂[ℂ]^n (Module.Dual ℂ Vector)) ≃ₗ[ℂ] (⨂[ℂ]^n Vector) :=
  PiTensorProduct.congr (fun _ : Fin n => dualCoordinates)

theorem powerCoordinates_action (n : ℕ) (g : Group)
    (x : ⨂[ℂ]^n (Module.Dual ℂ Vector)) :
    powerCoordinates n ((standard.dual.tensorPower n) g x) =
      (standard.tensorPower n) (inverseTranspose g) (powerCoordinates n x) := by
  suffices he : (powerCoordinates n).toLinearMap ∘ₗ (standard.dual.tensorPower n) g =
      (standard.tensorPower n) (inverseTranspose g) ∘ₗ (powerCoordinates n).toLinearMap from
    LinearMap.congr_fun he x
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change (PiTensorProduct.congr (fun _ : Fin n => dualCoordinates))
      ((standard.dual.tensorPower n) g (PiTensorProduct.tprod ℂ v)) =
    (standard.tensorPower n) (inverseTranspose g)
      (PiTensorProduct.congr (fun _ : Fin n => dualCoordinates) (PiTensorProduct.tprod ℂ v))
  simp only [Representation.tensorPower_apply,PiTensorProduct.map_tprod,
    PiTensorProduct.congr_tprod]
  congr 1
  funext i
  exact dualEquivalence.isIntertwining _ _ g (v i)

theorem permutation_image (n : ℕ)
    (f : Module.End ℂ (⨂[ℂ]^n (Module.Dual ℂ Vector)))
    (hf : ∀ g, Commute f ((standard.dual.tensorPower n) g)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
      (PiTensorProduct.reindexRepresentation ℂ (Module.Dual ℂ Vector) (Fin n)).asAlgebraHom a = f := by
  let e := powerCoordinates n
  let F := e.conj f
  have hc : ∀ g, Commute F ((standard.tensorPower n) g) := by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    have hfg := LinearMap.congr_fun (hf (inverseTranspose g)).eq y
    change f ((standard.dual.tensorPower n) (inverseTranspose g) y) =
      (standard.dual.tensorPower n) (inverseTranspose g) (f y) at hfg
    have he := powerCoordinates_action n (inverseTranspose g)
    rw [involution] at he
    change e (f (e.symm ((standard.tensorPower n) g (e y)))) =
      (standard.tensorPower n) g (e (f (e.symm (e y))))
    rw [← he y,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply,hfg]
    exact he (f y)
  obtain ⟨a,ha⟩ := SL3TensorCommutant.permutation_image n F hc
  refine ⟨a,?_⟩
  apply LinearMap.ext
  intro x
  apply e.injective
  have he := LinearMap.congr_fun ha (e x)
  have he' : F (e x) = e (f x) := by
    change e (f (e.symm (e x))) = e (f x)
    rw [LinearEquiv.symm_apply_apply]
  rw [← he',← he]
  clear ha he he' hc F
  induction a using MonoidAlgebra.induction_on with
  | of sigma =>
    simp only [Representation.asAlgebraHom_of,TauCeti.permTensorActionAlgHom_of,
      TauCeti.permTensorAction_apply,PiTensorProduct.reindexRepresentation_apply]
    suffices h : e.toLinearMap ∘ₗ
        (PiTensorProduct.reindex ℂ (fun _ : Fin n => Module.Dual ℂ Vector) sigma).toLinearMap =
      (PiTensorProduct.reindex ℂ (fun _ : Fin n => Vector) sigma).toLinearMap ∘ₗ e.toLinearMap from
      LinearMap.congr_fun h x
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change powerCoordinates n
        ((PiTensorProduct.reindex ℂ (fun _ : Fin n => Module.Dual ℂ Vector) sigma)
          (PiTensorProduct.tprod ℂ v)) =
      (PiTensorProduct.reindex ℂ (fun _ : Fin n => Vector) sigma)
        (powerCoordinates n (PiTensorProduct.tprod ℂ v))
    simp [powerCoordinates,PiTensorProduct.reindex_tprod,PiTensorProduct.congr_tprod]
  | add a b ha hb => simpa only [map_add,LinearMap.add_apply] using congrArg₂ (·+·) ha hb
  | smul z a ha => simpa only [map_smul,LinearMap.smul_apply] using congrArg (z • ·) ha

end
end Math.SL3DualTensorCommutant
