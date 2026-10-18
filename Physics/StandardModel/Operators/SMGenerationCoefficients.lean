import Physics.StandardModel.Operators.SMGenerationSupport
import Physics.StandardModel.Operators.SMCombinedCompactContinuity
import Physics.StandardModel.Operators.SMCombinedChargeSupport
import Math.RepresentationTheory.Characters.CompactCoefficientSupport
import Math.RepresentationTheory.ConstantPatternExterior

/-! Actual invariant coefficients from lower-half generation constituents.
No closed character, multiplicity or rank evaluation is used. -/
namespace GUT.SMGenerationCoefficients
set_option autoImplicit false
noncomputable section
open Math Representation SMGenerationCauchy ContinuousRepresentationScope
open FiniteBasisHilbertization ContinuousUnitaryConstructions
open scoped TensorProduct

attribute [local irreducible] TopExteriorCauchy.map SymmetricCauchy.map
  SU2SymmetricEmbeddings.omegaPower

@[reducible] local instance : AddCommGroup
    (SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    ((SMEpsilonTensor.Color ⊗[ℂ] WeakDoubletScalars.Doublet) ⊗[ℂ]
      WeakDoubletScalars.Doublet) := inferInstance
@[reducible] local instance : AddCommGroup
    (WeakDoubletScalars.Doublet ⊗[ℂ] WeakDoubletScalars.Doublet) := inferInstance

theorem inclusion_continuous : Continuous inclusion :=
  (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_const)).prodMk
    (continuous_snd.comp continuous_snd)

local instance : MeasurableSpace Group := borel Group
local instance : BorelSpace Group := ⟨rfl⟩

def continuousInclusion : Group →ₜ* SMCombinedCompactAction.Group :=
  ⟨inclusion, inclusion_continuous⟩

def weakDuality (m : ℕ) : Representation.Equiv (weak.symmetricPower m)
    (weak.symmetricPower m).dual :=
  (TwistedSU2ClebschGordan.symmetricPullback weakProjection WeakDoubletScalars.doublet m).trans
    ((SplitRepresentationProjection.restrictEquiv
      ((WeakDoubletScalars.duality m).trans
        (SplitRepresentationProjection.dualEquiv
          (SU2DoubletDuality.equivalence.symmetricPower m)).symm) weakProjection).trans
      { toLinearEquiv := .refl ℂ _
        isIntertwining' g := by ext phi x; rfl })

abbrev weakModel (m : ℕ) :=
  (TauCeti.SU2.symPowerModel m).toRepresentation.comp weakProjection

def weakModelEquiv (m : ℕ) : Representation.Equiv (weak.symmetricPower m) (weakModel m) where
  toLinearEquiv := TauCeti.SU2.weightEquiv m
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change TauCeti.SU2.weightEquiv m
      (WeakDoubletScalars.doublet.symmetricPower m (weakProjection g) x) = _
    rw [WeakDoubletScalars.symmetricPower_eq]
    exact (TauCeti.SU2.symPowerModelEquiv m).isIntertwining _ _ (weakProjection g) x

theorem weakModel_continuous (m : ℕ) : IsJointlyContinuous (weakModel m) := by
  apply ContinuousUnitaryConstructions.jointlyContinuous_of_orbit
  intro x
  exact (continuous_clm_apply.mp (TauCeti.SU2.continuous_symPowerModel m) x).comp
    (continuous_fst.comp continuous_snd)

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def sourceModelEquiv : Representation.Equiv
    ((SMCombinedCompactAction.source flavor p).comp inclusion)
    ((SMCombinedCompactContinuity.sourceModel flavor p).comp inclusion) :=
  SplitRepresentationProjection.restrictEquiv
    (basisCopyRepresentationEquiv (SMCombinedCompactContinuity.sourceBasis flavor p)
      (SMCombinedCompactAction.source flavor p)) inclusion

theorem sourceModel_continuous : IsJointlyContinuous
    ((SMCombinedCompactContinuity.sourceModel flavor p).comp inclusion) :=
  (SMCombinedCompactContinuity.source_continuous flavor p).comp continuousInclusion

theorem boson_restrict (m : ℕ) (delta : ℤ) :
    (SMCombinedCompactAction.boson (H := H) m delta).comp inclusion = weak.symmetricPower m := by
  ext g : 1
  apply LinearMap.ext
  intro x
  have hc : SMHiggsConstituents.character (H := H)
      (SMCombinedCompactAction.gaugeEmbedding (inclusion g)) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply, SMCombinedCompactAction.gaugeEmbedding,
      SMMixedCompactCoefficients.retained, inclusion, StandardSMGaugeTensor.phase]
  change (((SMHiggsConstituents.character ^ delta)
    (SMCombinedCompactAction.gaugeEmbedding (inclusion g)) : ℂˣ) •
      (WeakDoubletScalars.doublet.symmetricPower m) g.2.1 x) = _
  simp only [MonoidHom.zpow_apply, hc, one_zpow, one_smul]
  rfl

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv (weak.symmetricPower m)
    ((SMCombinedCompactAction.boson (H := H) m delta).comp inclusion) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by rw [boson_restrict]; rfl

def actionEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (Representation.tprod ((SMCombinedCompactAction.source flavor p).comp inclusion)
      (weak.symmetricPower m))
    ((SMCombinedCompactAction.action flavor p m delta).comp inclusion) where
  toLinearEquiv := TensorProduct.congr (.refl ℂ _) (bosonEquiv (H := H) m delta).toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change SMCombinedCompactAction.source flavor p (inclusion g) x ⊗ₜ[ℂ]
      bosonEquiv m delta (weak.symmetricPower m g y) = _
    exact congrArg (fun b => _ ⊗ₜ[ℂ] b)
      ((bosonEquiv (H := H) m delta).toIntertwiningMap.isIntertwining _ _ g y)

theorem restricted_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.action flavor p m delta).comp inclusion)) ↔
    SelectionCriteria.Allowed (IntertwiningMap (weak.symmetricPower m)
      ((SMCombinedCompactAction.source flavor p).comp inclusion)) :=
  (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (actionEquiv flavor p m delta))).symm.trans
    (CompactCoefficientSupport.coefficient_iff _ _ _ _
      (sourceModelEquiv flavor p) (weakModelEquiv m)
      (sourceModel_continuous flavor p) (weakModel_continuous m) (weakDuality m))

def sourceEquiv (s : DeltaLOneSignedInput.Species) (n : ℕ)
    (rho : Representation ℂ Group
      (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s))
    (hr : (SMCombinedCompactAction.field s).comp inclusion = rho) :
    Representation.Equiv (rho.exteriorPower n)
      ((SMCombinedCompactAction.source flavor (fun _ : Fin n => s)).comp inclusion) where
  toLinearEquiv := ConstantPatternExterior.linearEquiv SMCombinedCompactAction.field s n
  isIntertwining' g := by
    have he : rho.exteriorPower n g =
        (SMCombinedCompactAction.field s).exteriorPower n (inclusion g) := by
      change exteriorPower.map n (rho g) = _
      exact congrArg (exteriorPower.map n) (congrArg (fun r => r g) hr.symm)
    rw [he]
    exact (ConstantPatternExterior.equiv SMCombinedCompactAction.field s n).isIntertwining'
      (inclusion g)

include flavor in
theorem exterior_coefficient_iff (s : DeltaLOneSignedInput.Species) (n m : ℕ)
    (rho : Representation ℂ Group
      (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s))
    (hr : (SMCombinedCompactAction.field s).comp inclusion = rho) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((rho.exteriorPower n).tprod (weak.symmetricPower m))) ↔
    SelectionCriteria.Allowed (IntertwiningMap (weak.symmetricPower m) (rho.exteriorPower n)) :=
  CompactCoefficientSupport.coefficient_iff _ _ _ _
    ((sourceEquiv flavor s n rho hr).trans (sourceModelEquiv flavor (fun _ : Fin n => s)))
    (weakModelEquiv m) (sourceModel_continuous flavor (fun _ : Fin n => s))
    (weakModel_continuous m) (weakDuality m)

theorem local_of_nonzero_constituent (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (rho : Representation ℂ Group
      (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s))
    (hr : (SMCombinedCompactAction.field s).comp inclusion = rho)
    (hc : SMContentWeakBound.hypercharge (fun _ : Fin n => s) + 3*delta = 0)
    (h : SelectionCriteria.Allowed (IntertwiningMap (weak.symmetricPower m) (rho.exteriorPower n))) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (fun _ : Fin n => s) m delta)) := by
  have ht := (SelectionCriteria.allowed_equiv
    (InvariantTensorCurry.postcompose (weak.symmetricPower m) (rho.exteriorPower n)
      (sourceEquiv flavor s n rho hr))).mp h
  have hres := (restricted_iff flavor (fun _ : Fin n => s) m delta).mpr ht
  have hfull := SMCombinedChargeSupport.allowed flavor _ m delta hc hres
  exact (SelectionCriteria.allowed_equiv
    ((SMCombinedCompactAction.coefficientEquiv flavor _ m delta).trans
      (SMMixedCompactCoefficients.localEquiv flavor _ m delta).symm)).mp hfull

theorem local_of_constituent (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (rho : Representation ℂ Group
      (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s))
    (hr : (SMCombinedCompactAction.field s).comp inclusion = rho)
    (hc : SMContentWeakBound.hypercharge (fun _ : Fin n => s) + 3*delta = 0)
    (h : ∃ f : IntertwiningMap (weak.symmetricPower m) (rho.exteriorPower n),
      Function.Injective f) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (fun _ : Fin n => s) m delta)) := by
  obtain ⟨f,hf⟩ := h
  let t := (sourceEquiv flavor s n rho hr).toIntertwiningMap.comp f
  have hi : Function.Injective t := (sourceEquiv flavor s n rho hr).injective.comp hf
  have ht : t ≠ 0 := by
    intro he
    let : Nontrivial (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
      Module.nontrivial_of_finrank_pos (R := ℂ) (by
        change 0 < Module.finrank ℂ (Sym[ℂ]^m (Fin 2 → ℂ))
        rw [TauCeti.SU2.finrank_symPower]; omega)
    obtain ⟨x,hx⟩ := exists_ne (0 : Sym[ℂ]^m WeakDoubletScalars.Doublet)
    exact hx (hi (by rw [he]; rfl))
  have hres := (restricted_iff flavor (fun _ : Fin n => s) m delta).mpr ⟨t,ht⟩
  have hfull := SMCombinedChargeSupport.allowed flavor _ m delta hc hres
  exact (SelectionCriteria.allowed_equiv
    ((SMCombinedCompactAction.coefficientEquiv flavor _ m delta).trans
      (SMMixedCompactCoefficients.localEquiv flavor _ m delta).symm)).mp hfull

end
end GUT.SMGenerationCoefficients
