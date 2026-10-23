import Math.RepresentationTheory.Color.SU3.SU3VolumeContractions
import Math.RepresentationTheory.Color.SU3.SL3DualTensorCommutant
import Math.RepresentationTheory.Tensors.TensorContractionSpan
import Math.RepresentationTheory.Tensors.TensorPowerEquivalence

/-! Evaluation/volume spanning in both color orientations, on the actual
compact mixed sources. All commutant premises of the generic helper are proved. -/
namespace Math.SU3MixedContractionSpan
set_option autoImplicit false
noncomputable section
open Representation SL3ColorPlanes SL3CompactComparison ExternalInvariantTensor
open scoped TensorProduct

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance
@[reducible] local instance (a b : ℕ) : AddCommGroup (MixedCarrier a b) := inferInstance
@[reducible] local instance (a b : ℕ) : AddCommGroup
    ((⨂[ℂ]^a (Module.Dual ℂ Vector)) ⊗[ℂ] (⨂[ℂ]^b (Module.Dual ℂ (Module.Dual ℂ Vector)))) :=
  inferInstance

theorem defining_commutant : TensorContractionSpan.Commutant standard :=
  SL3TensorCommutant.permutation_image

theorem dual_commutant : TensorContractionSpan.Commutant standard.dual :=
  SL3DualTensorCommutant.permutation_image

def dualBasis := SU3VolumeContractions.basis.dualBasis

theorem dual_determinant (g : Group) : LinearMap.det (standard.dual g) = 1 := by
  change LinearMap.det (standard g⁻¹).dualMap = 1
  rw [LinearMap.det_dualMap,SU3VolumeContractions.determinant]

def dualSwap (p q : ℕ) : Representation.Equiv
    ((standard.dual.tensorPower p).tprod (standard.dual.dual.tensorPower q)) (mixed q p) :=
  (Representation.TensorProduct.comm _ _).trans
    (tensorEquiv
      (TensorPowerEquivalence.equivalence (SplitRepresentationProjection.bidualEquiv standard).symm q)
      (.refl (standard.dual.tensorPower p)))

theorem dualSwap_symm_tprod (p q : ℕ) (v : Fin q → Vector)
    (f : Fin p → Module.Dual ℂ Vector) :
    (dualSwap p q).symm (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => Module.Dual.eval ℂ Vector (v i)) := by
  change TensorProduct.comm ℂ _ _
    (TensorProduct.congr
      (TensorPowerEquivalence.equivalence (SplitRepresentationProjection.bidualEquiv standard).symm q).toLinearEquiv.symm
      (.refl ℂ _)
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f)) = _
  rw [TensorProduct.congr_tmul]
  change TensorProduct.comm ℂ _ _
    ((TensorPowerEquivalence.equivalence
      (SplitRepresentationProjection.bidualEquiv standard).symm q).symm
      (PiTensorProduct.tprod ℂ v) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) = _
  rw [TensorPowerEquivalence.symm_tprod]
  rfl

def compactRestriction (a b : ℕ)
    (f : InvariantCoefficientTransport.Invariants (mixed a b)) :
    InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed a b) where
  toLinearMap := f.toLinearMap
  isIntertwining' u := by
    apply LinearMap.ext
    intro x
    have he := f.isIntertwining _ _ (compactInclusion u) x
    have hm := congrArg (fun r => r u) (mixed_compact a b)
    exact hm ▸ he

def dualComplexContraction (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k))) :
    InvariantCoefficientTransport.Invariants (mixed q (q+3*k)) :=
  (TensorContractionSpan.contraction standard.dual dualBasis dual_determinant q k sigma).comp
    (dualSwap (q+3*k) q).symm.toIntertwiningMap

def dualContraction (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k))) :
    InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed q (q+3*k)) :=
  compactRestriction q (q+3*k) (dualComplexContraction q k sigma)

theorem dual_spanning (q k : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed q (q+3*k))) :
    ∃ c : Equiv.Perm (Fin (q+3*k)) → ℂ,
      f = ∑ sigma, c sigma • dualContraction q k sigma := by
  let F := (SU3BalancedContractions.extend q (q+3*k) f).comp
    (dualSwap (q+3*k) q).toIntertwiningMap
  obtain ⟨c,hc⟩ := TensorContractionSpan.spanning standard.dual dualBasis dual_determinant
    dual_commutant q k F
  refine ⟨c,?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f x = (∑ sigma, c sigma • dualContraction q k sigma) x
  have he := DFunLike.congr_fun hc ((dualSwap (q+3*k) q).symm x)
  change (SU3BalancedContractions.extend q (q+3*k) f)
      (dualSwap (q+3*k) q ((dualSwap (q+3*k) q).symm x)) = _ at he
  rw [Representation.Equiv.apply_symm_apply] at he
  simp only [IntertwiningMap.sum_apply,IntertwiningMap.smul_apply] at he ⊢
  exact he

end
end Math.SU3MixedContractionSpan
