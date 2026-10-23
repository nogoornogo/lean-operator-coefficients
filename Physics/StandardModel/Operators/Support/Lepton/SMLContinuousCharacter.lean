import Physics.StandardModel.Operators.Support.Lepton.SMLWeightExpansion
import Math.RepresentationTheory.Exterior.ExteriorContinuity
import Math.RepresentationTheory.SU2.SL2SpanContinuity
import Math.RepresentationTheory.Unitary.ContinuousConstructions

/-! Analytic copies for the actual L polynomial action. -/
namespace Physics.SMLContinuousCharacter
set_option autoImplicit false
noncomputable section
open Math Representation FiniteBasisHilbertization ContinuousUnitaryConstructions
open scoped TensorProduct
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev fieldAction : Representation ℂ (TauCeti.SU2 × TauCeti.SU2)
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) 3) :=
  (DeltaLOneSignedFields.field flavor 3).comp SMLWeightExpansion.pairInclusion

abbrev fieldCopy := Copy (SMWeakWeightBasis.fieldBasis (3 : DeltaLOneSignedInput.Species))

theorem field_basis_coordinates (k : TauCeti.SU2 × TauCeti.SU2)
    (i j : SMWeakWeightBasis.FieldIndex (3 : DeltaLOneSignedInput.Species)) :
    (SMWeakWeightBasis.fieldBasis 3).repr
      (fieldAction flavor k (SMWeakWeightBasis.fieldBasis 3 i)) j =
      (k.1 : Matrix (Fin 2) (Fin 2) ℂ) j.1.1 i.1.1 *
        (k.2 : Matrix (Fin 2) (Fin 2) ℂ) j.1.2 i.1.2 * (if j.2=i.2 then 1 else 0) := by
  rcases i with ⟨⟨a,b⟩,c⟩
  rcases j with ⟨⟨d,e⟩,f⟩
  simp [fieldAction, SMWeakWeightBasis.fieldBasis, SMWeakWeightBasis.gaugeBasis,
    DeltaLOneSignedFields.field, DeltaLOneSignedFields.localField,
    ExternalInvariantTensor.external, SMLWeightExpansion.pairInclusion,
    StandardSMGaugeTensor.lepton, StandardSMGaugeTensor.twist,
    StandardSMGaugeTensor.phase, StandardSMGaugeTensor.weak,
    FourSameWeylCompleteness.action, DeltaLOneSignedFields.rightHanded, WeylSpinor.left,
    SL2SymmetricEmbeddings.compactInclusion, Representation.tprod_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, Matrix.toLin'_apply,
    Pi.basisFun_apply, Pi.single_apply, mul_comm]
  rfl

theorem field_continuous : ContinuousRepresentationScope.IsJointlyContinuous
    (basisCopyRepresentation (SMWeakWeightBasis.fieldBasis 3) (fieldAction flavor)) := by
  apply basisCopyRepresentation_jointlyContinuous
  intro i
  let e := Copy.coordinateEquiv (SMWeakWeightBasis.fieldBasis (3 : DeltaLOneSignedInput.Species))
  have hc : Continuous (fun k => e (⟨fieldAction flavor k (SMWeakWeightBasis.fieldBasis 3 i)⟩ : fieldCopy)) := by
    change Continuous (fun k => WithLp.toLp 2 (fun j =>
      (SMWeakWeightBasis.fieldBasis 3).repr
        (fieldAction flavor k (SMWeakWeightBasis.fieldBasis 3 i)) j))
    apply (PiLp.continuous_toLp 2 (fun _ : SMWeakWeightBasis.FieldIndex 3 => ℂ)).comp
    apply continuous_pi
    intro j
    change Continuous (fun k => (SMWeakWeightBasis.fieldBasis 3).repr
      (fieldAction flavor k (SMWeakWeightBasis.fieldBasis 3 i)) j)
    have he : (fun k => (SMWeakWeightBasis.fieldBasis 3).repr
        (fieldAction flavor k (SMWeakWeightBasis.fieldBasis 3 i)) j) =
        fun k => (k.1 : Matrix (Fin 2) (Fin 2) ℂ) j.1.1 i.1.1 *
          (k.2 : Matrix (Fin 2) (Fin 2) ℂ) j.1.2 i.1.2 * (if j.2=i.2 then 1 else 0) :=
      funext (fun k => field_basis_coordinates flavor k i j)
    rw [he]
    have hu : Continuous (fun k : TauCeti.SU2 × TauCeti.SU2 =>
        (k.1 : Matrix (Fin 2) (Fin 2) ℂ) j.1.1 i.1.1) :=
      (show Continuous (fun a : Fin 2 → Fin 2 → ℂ => a j.1.1 i.1.1) from
        (continuous_apply i.1.1).comp (continuous_apply j.1.1)).comp
        (show Continuous (fun k : TauCeti.SU2 × TauCeti.SU2 =>
          (k.1 : Matrix (Fin 2) (Fin 2) ℂ)) from
            continuous_subtype_val.comp continuous_fst)
    have hv : Continuous (fun k : TauCeti.SU2 × TauCeti.SU2 =>
        (k.2 : Matrix (Fin 2) (Fin 2) ℂ) j.1.2 i.1.2) :=
      (show Continuous (fun a : Fin 2 → Fin 2 → ℂ => a j.1.2 i.1.2) from
        (continuous_apply i.1.2).comp (continuous_apply j.1.2)).comp
        (show Continuous (fun k : TauCeti.SU2 × TauCeti.SU2 =>
          (k.2 : Matrix (Fin 2) (Fin 2) ℂ)) from
            continuous_subtype_val.comp continuous_snd)
    exact (hu.mul hv).mul continuous_const
  have hd := e.symm.toLinearMap.continuous_of_finiteDimensional.comp hc
  convert hd using 1
  funext k
  exact (e.symm_apply_apply _).symm

local instance fieldFinite (s : DeltaLOneSignedInput.Species) :
    FiniteDimensional ℂ (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field, ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance

local instance sourceFinite (n : ℕ) : FiniteDimensional ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (SMLCompactWeyl.pattern n)) := by
  change FiniteDimensional ℂ (LinearMap.range (PatternExteriorSource.map
    (DeltaLOneSignedFields.field flavor) (SMLCompactWeyl.pattern n)).toLinearMap)
  infer_instance

abbrev sourceAction (n : ℕ) : Representation ℂ (TauCeti.SU2 × TauCeti.SU2)
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (SMLCompactWeyl.pattern n)) :=
  (SMLCompactWeyl.source flavor n).comp SMLWeightExpansion.pairInclusion

def sourceBasis (n : ℕ) := Module.finBasis ℂ
  (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) (SMLCompactWeyl.pattern n))
abbrev sourceCopy (n : ℕ) := Copy (sourceBasis flavor n)
abbrev sourceModel (n : ℕ) := basisCopyRepresentation (sourceBasis flavor n) (sourceAction flavor n)

def exteriorModelEquiv (n : ℕ) : Representation.Equiv
    ((basisCopyRepresentation (SMWeakWeightBasis.fieldBasis 3) (fieldAction flavor)).exteriorPower n)
      (sourceModel flavor n) :=
  ((basisCopyRepresentationEquiv (SMWeakWeightBasis.fieldBasis 3) (fieldAction flavor)).symm.exteriorPower n).trans
    ((SplitRepresentationProjection.restrictEquiv
      (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) 3 n)
        SMLWeightExpansion.pairInclusion).trans
      (basisCopyRepresentationEquiv (sourceBasis flavor n) (sourceAction flavor n)))

theorem source_continuous (n : ℕ) : ContinuousRepresentationScope.IsJointlyContinuous
    (sourceModel flavor n) := by
  exact ExteriorContinuity.representation_continuous
    (basisCopyRepresentation (SMWeakWeightBasis.fieldBasis 3) (fieldAction flavor))
    (field_continuous flavor).orbit n (sourceModel flavor n) (exteriorModelEquiv flavor n)

abbrev bosonAction (m : ℕ) (delta : ℤ) : Representation ℂ (TauCeti.SU2 × TauCeti.SU2)
    (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
  (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
    SMHiggsConstituents.character m delta).comp SMLWeightExpansion.pairInclusion

theorem boson_apply (m : ℕ) (delta : ℤ) (k : TauCeti.SU2 × TauCeti.SU2)
    (x : Sym[ℂ]^m WeakDoubletScalars.Doublet) : bosonAction (H := H) m delta k x =
      TauCeti.SU2.symPower m k.1 x := by
  have hh : SMHiggsConstituents.character (H := H) (SMLWeightExpansion.pairInclusion k) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply, SMLWeightExpansion.pairInclusion,
      StandardSMGaugeTensor.phase]
  change ((SMHiggsConstituents.character ^ delta) (SMLWeightExpansion.pairInclusion k) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) k.1 x = _
  rw [MonoidHom.zpow_apply, hh, one_zpow, one_smul, WeakDoubletScalars.symmetricPower_eq]

abbrev bosonModel (m : ℕ) : Representation ℂ (TauCeti.SU2 × TauCeti.SU2)
    (EuclideanSpace ℂ (Fin (m+1))) :=
  (TauCeti.SU2.symPowerModel m).toRepresentation.comp (MonoidHom.fst _ _)

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (bosonAction (H := H) m delta) (bosonModel m) where
  toLinearEquiv := TauCeti.SU2.weightEquiv m
  isIntertwining' k := by
    apply LinearMap.ext
    intro x
    change TauCeti.SU2.weightEquiv m (bosonAction (H := H) m delta k x) = _
    rw [boson_apply]
    exact (TauCeti.SU2.symPowerModelEquiv m).isIntertwining _ _ k.1 x

theorem boson_continuous (m : ℕ) : ContinuousRepresentationScope.IsJointlyContinuous
    (bosonModel m) := by
  apply jointlyContinuous_of_orbit
  intro x
  exact (continuous_clm_apply.mp (TauCeti.SU2.continuous_symPowerModel m) x).comp continuous_fst

abbrev model (n m : ℕ) := (sourceModel flavor n).tprod (bosonModel m)

def equiv (n m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMLWeightExpansion.action flavor n m delta) (model flavor n m) where
  toLinearEquiv := TensorProduct.congr
    (Copy.valLinearEquiv (sourceBasis flavor n)).symm (TauCeti.SU2.weightEquiv m)
  isIntertwining' k := by
    apply TensorProduct.ext'
    intro x y
    change (Copy.valLinearEquiv (sourceBasis flavor n)).symm (sourceAction flavor n k x) ⊗ₜ[ℂ]
      TauCeti.SU2.weightEquiv m (bosonAction (H := H) m delta k y) =
      sourceModel flavor n k ((Copy.valLinearEquiv (sourceBasis flavor n)).symm x) ⊗ₜ[ℂ]
        bosonModel m k (TauCeti.SU2.weightEquiv m y)
    exact congrArg₂ (fun u v => u ⊗ₜ[ℂ] v)
      ((basisCopyRepresentationEquiv (sourceBasis flavor n) (sourceAction flavor n)).isIntertwining _ _ k x)
      ((bosonEquiv (H := H) m delta).isIntertwining _ _ k y)

theorem continuous_model (n m : ℕ) : ContinuousRepresentationScope.IsJointlyContinuous
    (model flavor n m) := jointlyContinuous_tprod _ _
      (source_continuous flavor n) (boson_continuous m)

def weights (n m : ℕ) : ℕ × ℕ →₀ ℂ := SU2SignedWeights.coefficients
  (fun _ : SMLWeightExpansion.Indices n m => 1)
  (SMLWeightExpansion.totalWeak n m) (SMLWeightExpansion.totalSpin n m)

/-- The actual L/Higgs weak/Weyl coefficient multiplicity, uniformly in n,m. -/
theorem coefficient_dimension (n m : ℕ) (delta : ℤ) :
    (Module.finrank ℂ (InvariantCoefficientTransport.Invariants
      (SMLWeightExpansion.action flavor n m delta)) : ℂ) =
      weights n m (0,0) - weights n m (0,2) - weights n m (2,0) + weights n m (2,2) := by
  rw [(InvariantCoefficientTransport.alongEquiv (equiv flavor n m delta)).finrank_eq]
  apply SU2SignedWeights.coefficient_finrank _ (continuous_model flavor n m)
  · intro z w
    rw [← Representation.char_iso (equiv flavor n m delta)]
    simpa only [one_mul] using SMLWeightExpansion.torus_character flavor n m delta z w
  · intro z w
    have h := Representation.char_conj (model flavor n m)
      (TauCeti.SU2.torusHom z,TauCeti.SU2.torusHom w) (TauCeti.SU2.weylElement,1)
    simpa only [Prod.mk_mul_mk, Prod.inv_mk, one_mul, mul_one, inv_one,
      TauCeti.SU2.weylElement_conj_torusHom] using h
  · intro z w
    have h := Representation.char_conj (model flavor n m)
      (TauCeti.SU2.torusHom z,TauCeti.SU2.torusHom w) (1,TauCeti.SU2.weylElement)
    simpa only [Prod.mk_mul_mk, Prod.inv_mk, one_mul, mul_one, inv_one,
      TauCeti.SU2.weylElement_conj_torusHom] using h

end
end Physics.SMLContinuousCharacter
