import Physics.StandardModel.Operators.SMLKernelDimension
import Physics.StandardModel.Operators.BnvLocalConjugation
import Physics.StandardModel.Gauge.DipoleGaugeTensor

/-! Conjugate-L local transport retains the hypercharge sign reversal. -/
namespace GUT.SMLConjugateMultiplicity
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights
open scoped TensorProduct
variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def fieldEquiv : Representation.Equiv
    ((DeltaLOneSignedFields.field flavor 8).comp (MonoidHom.inl Group H))
    (((DeltaLOneSignedFields.field flavor 3).comp (MonoidHom.inl Group H)).comp BnvLocalConjugation.conjugate) where
  toLinearEquiv := TensorProduct.congr (BnvLocalConjugation.localField 8).toLinearEquiv
    (LinearEquiv.refl ℂ (Fin 3 → ℂ))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x v
    change (BnvLocalConjugation.localField 8) (DeltaLOneSignedFields.localField 8 g x) ⊗ₜ[ℂ]
      (flavor 8 1 v) =
      DeltaLOneSignedFields.localField 3 (BnvLocalConjugation.conjugate g)
        ((BnvLocalConjugation.localField 8) x) ⊗ₜ[ℂ] (flavor 3 1 v)
    rw [map_one, map_one]
    exact congrArg (fun x => x ⊗ₜ[ℂ] v) ((BnvLocalConjugation.localField 8).isIntertwining _ _ g x)

def sourceEquiv (n : ℕ) : Representation.Equiv
    (SMIntegralLocalWeights.source flavor (SMConstantContentRanks.pattern 8 n))
    ((SMIntegralLocalWeights.source flavor (SMConstantContentRanks.pattern 3 n)).comp
      BnvLocalConjugation.conjugate) :=
  (SplitRepresentationProjection.restrictEquiv
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 8 n)
      (MonoidHom.inl Group H)).symm.trans
    ((fieldEquiv flavor).exteriorPower n |>.trans
      (SplitRepresentationProjection.restrictEquiv
        (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 3 n)
          ((MonoidHom.inl Group H).comp BnvLocalConjugation.conjugate)))

def weakConjugate : Representation.Equiv WeakDoubletScalars.doublet
    (WeakDoubletScalars.doublet.comp (SpecialUnitaryContragredient.conjugate 2)) :=
  DipoleGaugeTensor.weakDualEquiv.trans (SpecialUnitaryContragredient.dualEquiv 2)

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.boson (H := H) m delta)
    ((SMIntegralLocalWeights.boson (H := H) m (-delta)).comp BnvLocalConjugation.conjugate) where
  toLinearEquiv := (weakConjugate.symmetricPower m).toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change (weakConjugate.symmetricPower m)
      (((SMHiggsConstituents.character (H := H) ^ delta) (g,1) : ℂˣ) •
        (WeakDoubletScalars.doublet.symmetricPower m) g.1.2.1 x) =
      ((SMHiggsConstituents.character (H := H) ^ (-delta)) (BnvLocalConjugation.conjugate g,1) : ℂˣ) •
        (WeakDoubletScalars.doublet.symmetricPower m)
          (SpecialUnitaryContragredient.conjugate 2 g.1.2.1) ((weakConjugate.symmetricPower m) x)
    have hc : ((SMHiggsConstituents.character (H := H) ^ delta) (g,1) : ℂˣ) =
        ((SMHiggsConstituents.character (H := H) ^ (-delta)) (BnvLocalConjugation.conjugate g,1) : ℂˣ) := by
      apply Units.ext
      simp [MonoidHom.zpow_apply, SMHiggsConstituents.character_apply,
        BnvLocalConjugation.conjugate, SMGaugeConjugation.conjugate,
        StandardSMGaugeTensor.phase, zpow_neg]
    rw [hc]
    simp only [Units.smul_def, map_smul]
    exact congrArg (fun y => _ • y) ((weakConjugate.symmetricPower m).isIntertwining _ _ g.1.2.1 x)

def actionEquiv (n m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 8 n) m delta)
    ((SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 3 n) m (-delta)).comp
      BnvLocalConjugation.conjugate) :=
  BnvLocalConjugation.tensor (sourceEquiv flavor n) (bosonEquiv (H := H) m delta)

def coefficientEquiv (n m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 8 n) m delta) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 3 n) m (-delta)) :=
  (InvariantCoefficientTransport.alongEquiv (actionEquiv flavor n m delta)).trans
    (InvariantCoefficientTransport.alongSurjection _ _ BnvLocalConjugation.surjective)

theorem allowed_iff (n m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (SMConstantContentRanks.pattern 8 n) m delta)) ↔
        delta = -(n : ℤ) ∧ SMLKernelDimension.multiplicity n m ≠ 0 := by
  exact (SelectionCriteria.allowed_equiv (coefficientEquiv flavor n m delta)).trans
    ((SMLKernelDimension.allowed_iff flavor n m (-delta)).trans (by
      constructor <;> rintro ⟨hn,hp⟩ <;> exact ⟨by omega, hp⟩))

theorem kernel_dimension (n m : ℕ) (delta : ℤ) (hn : delta = -(n : ℤ)) :
    (Module.finrank ℂ (SMFullLocalKernel.Kernel flavor (SMConstantContentRanks.pattern 8 n) m delta) : ℂ) =
      SMLKernelDimension.multiplicity n m := by
  have e := (SMFullLocalKernel.coefficientEquiv flavor (SMConstantContentRanks.pattern 8 n) m delta).symm.trans
    ((coefficientEquiv flavor n m delta).trans
      (SMFullLocalKernel.coefficientEquiv flavor (SMConstantContentRanks.pattern 3 n) m (-delta)))
  exact (congrArg (fun d : ℕ => (d : ℂ)) e.finrank_eq).trans
    (SMLKernelDimension.kernel_dimension flavor n m (-delta) (by omega))

end
end GUT.SMLConjugateMultiplicity
