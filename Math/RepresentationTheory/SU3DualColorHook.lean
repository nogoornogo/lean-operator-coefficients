import Math.RepresentationTheory.ExteriorCubeHook
import Math.RepresentationTheory.SU3ColorPair
import Math.RepresentationTheory.SU3DualExterior

/-! Identify the actual dual-color cubic hook kernel with trace-free endomorphisms.
This uses complementary exterior duality and rank-one trace, without
assuming adjoint irreducibility. -/
namespace Math.SU3DualColorHook
set_option autoImplicit false
noncomputable section
open Representation
abbrev rho := SU3DualExterior.rho
abbrev Vector := SU3DualExterior.Vector
abbrev volume := SU3DualExterior.volume

theorem dimension : Module.finrank ℂ Vector=3 := by
  rw [Subspace.dual_finrank_eq,SU3DefiningExterior.dimension]

def twoEquiv : Representation.Equiv (rho.exteriorPower 2) rho.dual :=
  (ComplementaryExteriorDuality.equiv rho SU3DualExterior.determinant volume (by rw [dimension])).trans
    (SplitRepresentationProjection.dualEquiv rho.exteriorPowerOneEquiv)
open scoped TensorProduct
open TensorSquareQuotients ExteriorCubeHook
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance : AddCommGroup (Source (V := Vector)) := inferInstance

private def castVolume {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (h : n=Module.finrank ℂ V)
    (vol : (⋀[ℂ]^(Module.finrank ℂ V) V) ≃ₗ[ℂ] ℂ) : (⋀[ℂ]^n V) ≃ₗ[ℂ] ℂ := h ▸ vol

private theorem castVolume_coe {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (h : n=Module.finrank ℂ V)
    (vol : (⋀[ℂ]^(Module.finrank ℂ V) V) ≃ₗ[ℂ] ℂ) :
    (castVolume h vol).toLinearMap=(h ▸ vol.toLinearMap) := by
  subst n
  rfl

def volume3 : (⋀[ℂ]^3 Vector) ≃ₗ[ℂ] ℂ :=
  castVolume (show 3=Module.finrank ℂ Vector by rw [dimension]) volume

def endEquiv : Representation.Equiv (ExteriorCubeHookRepresentation.source rho)
    (TraceEndomorphismSplit.action rho) :=
  (ExternalInvariantTensor.tensorEquiv (.refl rho) twoEquiv).trans
    ((Representation.TensorProduct.comm rho rho.dual).trans
      (Representation.Equiv.dualTensorHom rho rho))

@[simp] theorem endEquiv_pure (a : Vector) (x : ⋀[ℂ]^2 Vector) :
    endEquiv (a ⊗ₜ[ℂ] x)=(twoEquiv x).smulRight a := by
  ext z
  rfl

theorem wedge21 (a b c : Vector) :
    exteriorPower.wedge ℂ Vector 2 1 (wedge (b ⊗ₜ[ℂ] c))
      ((exteriorPower.oneEquiv ℂ Vector).symm a)=cube b c a := by
  apply Subtype.ext
  simp [exteriorPower.wedge,ExteriorSquareTensorDescent.wedge_tmul,
    exteriorPower.oneEquiv_symm_apply,cube,ExteriorAlgebra.ιMulti_succ_apply,mul_assoc]

theorem twoEquiv_evaluate (a b c : Vector) :
    twoEquiv (wedge (b ⊗ₜ[ℂ] c)) a=volume3 (cube a b c) := by
  change exteriorPower.wedgePairing volume (by rw [dimension] : 2+1=Module.finrank ℂ Vector)
      (wedge (b ⊗ₜ[ℂ] c)) (rho.exteriorPowerOneEquiv.symm a)=volume3 (cube a b c)
  rw [show rho.exteriorPowerOneEquiv.symm a=(exteriorPower.oneEquiv ℂ Vector).symm a from rfl]
  simp only [exteriorPower.wedgePairing,LinearMap.compr₂_apply]
  rw [← castVolume_coe]
  change volume3 (exteriorPower.wedge ℂ Vector 2 1 (wedge (b ⊗ₜ[ℂ] c))
    ((exteriorPower.oneEquiv ℂ Vector).symm a))=volume3 (cube a b c)
  rw [wedge21,← cube_cycle b c a]

/-- Trace corresponds exactly to the exterior-cube quotient, for the same
chosen volume as the existing complementary duality. -/
theorem trace_multiply (x : Source (V := Vector)) :
    LinearMap.trace ℂ Vector (endEquiv x)=volume3 (multiply x) := by
  have h : (LinearMap.trace ℂ Vector).comp endEquiv.toLinearEquiv.toLinearMap=
      volume3.toLinearMap.comp multiply := by
    apply TensorProduct.ext'
    intro a y
    have ha : ((LinearMap.trace ℂ Vector).comp endEquiv.toLinearEquiv.toLinearMap).comp
        (TensorProduct.mk ℂ Vector (⋀[ℂ]^2 Vector) a)=
        (volume3.toLinearMap.comp multiply).comp
        (TensorProduct.mk ℂ Vector (⋀[ℂ]^2 Vector) a) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change LinearMap.trace ℂ Vector (endEquiv (a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v))=
        volume3 (multiply (a ⊗ₜ[ℂ] exteriorPower.ιMulti ℂ 2 v))
      rw [← wedge_eta v,endEquiv_pure,LinearMap.trace_smulRight,twoEquiv_evaluate,multiply_pure]
    exact LinearMap.congr_fun ha y
  exact LinearMap.congr_fun h x

def equivalence : Representation.Equiv (ExteriorCubeHookRepresentation.action rho) (TraceEndomorphismSplit.traceFreeAction rho) where
  toLinearEquiv :=
    { toFun x := ⟨endEquiv x.val,by
        change LinearMap.trace ℂ Vector (endEquiv x.val)=0
        rw [trace_multiply,show multiply x.val=0 from x.property,map_zero]⟩
      invFun x := ⟨endEquiv.symm x.val,by
        change multiply (endEquiv.symm x.val)=0
        apply volume3.injective
        rw [map_zero,← trace_multiply,endEquiv.apply_symm_apply]
        exact x.property⟩
      left_inv x := by apply Subtype.ext; exact endEquiv.symm_apply_apply x.val
      right_inv x := by apply Subtype.ext; exact endEquiv.apply_symm_apply x.val
      map_add' x y := by apply Subtype.ext; exact map_add endEquiv x.val y.val
      map_smul' z x := by apply Subtype.ext; exact map_smul endEquiv z x.val }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact endEquiv.isIntertwining _ _ g x.val

end
end Math.SU3DualColorHook
