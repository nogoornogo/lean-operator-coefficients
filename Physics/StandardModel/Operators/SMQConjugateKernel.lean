import Physics.StandardModel.Operators.SMQGaussianKernel
import Physics.StandardModel.Operators.SMLConjugateMultiplicity
import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Gauge.DipoleGaugeTensor

/-! Conjugate-Q local transport retains the hypercharge sign reversal. -/
namespace GUT.SMQConjugateKernel
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights
open scoped TensorProduct
variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def fieldEquiv : Representation.Equiv
    ((DeltaLOneSignedFields.field flavor 5).comp (MonoidHom.inl Group H))
    (((DeltaLOneSignedFields.field flavor 0).comp (MonoidHom.inl Group H)).comp BnvLocalConjugation.conjugate) where
  toLinearEquiv := TensorProduct.congr (BnvLocalConjugation.localField 5).toLinearEquiv
    (LinearEquiv.refl ℂ (Fin 3 → ℂ))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x v
    change (BnvLocalConjugation.localField 5) (DeltaLOneSignedFields.localField 5 g x) ⊗ₜ[ℂ]
      (flavor 5 1 v) =
      DeltaLOneSignedFields.localField 0 (BnvLocalConjugation.conjugate g)
        ((BnvLocalConjugation.localField 5) x) ⊗ₜ[ℂ] (flavor 0 1 v)
    rw [map_one, map_one]
    exact congrArg (fun x => x ⊗ₜ[ℂ] v) ((BnvLocalConjugation.localField 5).isIntertwining _ _ g x)

def sourceEquiv (n : ℕ) : Representation.Equiv
    (SMIntegralLocalWeights.source flavor (SMConstantContentRanks.pattern 5 n))
    ((SMIntegralLocalWeights.source flavor (SMConstantContentRanks.pattern 0 n)).comp
      BnvLocalConjugation.conjugate) :=
  (SplitRepresentationProjection.restrictEquiv
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 5 n)
      (MonoidHom.inl Group H)).symm.trans
    ((fieldEquiv flavor).exteriorPower n |>.trans
      (SplitRepresentationProjection.restrictEquiv
        (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 0 n)
          ((MonoidHom.inl Group H).comp BnvLocalConjugation.conjugate)))

def actionEquiv (n m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 5 n) m delta)
    ((SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 0 n) m (-delta)).comp
      BnvLocalConjugation.conjugate) :=
  BnvLocalConjugation.tensor (sourceEquiv flavor n) (SMLConjugateMultiplicity.bosonEquiv (H := H) m delta)

def coefficientEquiv (n m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 5 n) m delta) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 0 n) m (-delta)) :=
  (InvariantCoefficientTransport.alongEquiv (actionEquiv flavor n m delta)).trans
    (InvariantCoefficientTransport.alongSurjection _ _ BnvLocalConjugation.surjective)

theorem coefficient_dimension (n m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 5 n) m delta)) =
        (SMQGaussianKernel.polynomial n m (-delta)).natTrailingDegree :=
  (coefficientEquiv flavor n m delta).finrank_eq.trans
    (SMQGaussianKernel.coefficient_dimension flavor n m (-delta))

theorem allowed_iff (n m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 5 n) m delta)) ↔
        (SMQGaussianKernel.polynomial n m (-delta)).coeff 0 = 0 :=
  (SelectionCriteria.allowed_equiv (coefficientEquiv flavor n m delta)).trans
    (SMQGaussianKernel.allowed_iff flavor n m (-delta))

theorem kernel_dimension (n m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (SMConstantContentRanks.pattern 5 n) m delta) =
      (SMQGaussianKernel.polynomial n m (-delta)).natTrailingDegree :=
  (SMFullLocalKernel.coefficientEquiv flavor (SMConstantContentRanks.pattern 5 n) m delta).finrank_eq.symm.trans
    (coefficient_dimension flavor n m delta)

theorem rank_add_nullity (n m : ℕ) (delta : ℤ) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor
      (SMConstantContentRanks.pattern 5 n) m delta)) +
        (SMQGaussianKernel.polynomial n m (-delta)).natTrailingDegree =
          SMConstantContentRanks.columns 5 n m := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (SMFullLocalKernel.constraints flavor (SMConstantContentRanks.pattern 5 n) m delta)
  have hd : Module.finrank ℂ
      (Fin (Module.finrank ℂ (SMFullLocalKernel.Carrier flavor (SMConstantContentRanks.pattern 5 n) m)) → ℂ) =
      SMConstantContentRanks.columns 5 n m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact SMConstantContentRanks.carrier_dimension flavor 5 n m
  exact (congrArg (fun k : ℕ => Module.finrank ℂ (LinearMap.range
    (SMFullLocalKernel.constraints flavor (SMConstantContentRanks.pattern 5 n) m delta)) + k)
      (kernel_dimension flavor n m delta)).symm.trans (h.trans hd)

end
end GUT.SMQConjugateKernel
