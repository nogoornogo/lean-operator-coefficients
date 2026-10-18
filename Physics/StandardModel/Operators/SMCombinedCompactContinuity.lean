import Physics.StandardModel.Operators.SMCombinedCompactAction
import Math.RepresentationTheory.BasisActionContinuity
import TauCeti.RepresentationTheory.SU2.Exhaustion
import TauCeti.Topology.Algebra.UnitaryGroup

/-! Finite analytic models of the combined actual compact action. -/
namespace GUT.SMCombinedCompactContinuity
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor SMWeakWeightBasis
open FiniteBasisHilbertization ContinuousUnitaryConstructions BasisActionContinuity
open scoped TensorProduct

private theorem entry_continuous {A : Type*} [TopologicalSpace A] {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ → Prop}
    (u : A → {M // P M}) (hu : Continuous u) (i j : Fin d) :
    Continuous (fun a => (u a : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (show Continuous (fun a : Fin d → Fin d → ℂ => a i j) from
    (continuous_apply j).comp (continuous_apply i)).comp ((show Continuous (Subtype.val : {M // P M} → Matrix (Fin d) (Fin d) ℂ) from
      continuous_subtype_val).comp hu)

theorem color_coefficients : Coefficients (Pi.basisFun ℂ (Fin 3)) color := by
  intro i j
  have hc : Continuous (fun g : GaugeGroup => (g.1 : Matrix (Fin 3) (Fin 3) ℂ) j i) := entry_continuous _ continuous_fst j i
  simpa [color,Matrix.toLin'_apply,Pi.basisFun_apply] using hc

theorem weak_coefficients : Coefficients (Pi.basisFun ℂ (Fin 2)) weak := by
  intro i j
  have hc : Continuous (fun g : GaugeGroup => (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) j i) := entry_continuous _ (continuous_fst.comp continuous_snd) j i
  simpa [weak,Matrix.toLin'_apply,Pi.basisFun_apply] using hc

theorem phase_continuous (y : ℤ) : Continuous (phase y) := by
  change Continuous (fun g : GaugeGroup => ((g.2.2 ^ y : Circle) : ℂ))
  have hz : Continuous (fun g : GaugeGroup => g.2.2) := continuous_snd.comp continuous_snd
  exact continuous_subtype_val.comp (hz.zpow y)

variable {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℂ V]
omit [Fintype I] in
theorem twist_coefficients (b : Module.Basis I ℂ V) (rho : Representation ℂ GaugeGroup V)
    (hr : Coefficients b rho) (y : ℤ) : Coefficients b (twist rho y) := by
  intro i j
  change Continuous (fun g => b.repr (phase y g • rho g (b i)) j)
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul]
  exact (phase_continuous y).mul (hr i j)

theorem gauge_coefficients (s : DeltaLOneSignedInput.Species) :
    Coefficients (gaugeBasis s) (DeltaLOneSignedFields.gauge s) := by
  have hq := twist_coefficients quarkBasis (color.tprod weak)
    (BasisActionContinuity.tensor _ _ _ _ color_coefficients weak_coefficients) 1
  have hu := twist_coefficients (Pi.basisFun ℂ (Fin 3)) color color_coefficients 4
  have hd := twist_coefficients (Pi.basisFun ℂ (Fin 3)) color color_coefficients (-2)
  have hl := twist_coefficients (Pi.basisFun ℂ (Fin 2)) weak weak_coefficients (-3)
  have he := twist_coefficients scalarBasis (Representation.trivial ℂ GaugeGroup ℂ)
    (BasisActionContinuity.trivial _) (-6)
  fin_cases s
  · exact hq
  · exact hu
  · exact hd
  · exact hl
  · exact he
  · exact BasisActionContinuity.dual _ _ hq
  · exact BasisActionContinuity.dual _ _ hu
  · exact BasisActionContinuity.dual _ _ hd
  · exact BasisActionContinuity.dual _ _ hl
  · exact BasisActionContinuity.dual _ _ he

theorem spin_coefficients (right : Bool) : Coefficients (Pi.basisFun ℂ (Fin 2))
    ((WeylIndependentAction.spin right).comp SMMixedCompactWeyl.compact) := by
  intro i j
  cases right
  · have hc : Continuous (fun g : SMCombinedCompactAction.Spin =>
        (g.1 : Matrix (Fin 2) (Fin 2) ℂ) j i) := entry_continuous _ continuous_fst j i
    convert hc using 1
    funext g
    simp [WeylIndependentAction.spin,SMMixedCompactWeyl.compact,WeylSpinor.left,
      SL2SymmetricEmbeddings.compactInclusion,Matrix.toLin'_apply,Pi.basisFun_apply]
    rfl
  · have hc : Continuous (fun g : SMCombinedCompactAction.Spin =>
        (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j i) := entry_continuous _ continuous_snd j i
    convert hc using 1
    funext g
    simp [WeylIndependentAction.spin,SMMixedCompactWeyl.compact,WeylSpinor.left,
      SL2SymmetricEmbeddings.compactInclusion,Matrix.toLin'_apply,Pi.basisFun_apply]
    rfl

theorem field_coefficients (s : DeltaLOneSignedInput.Species) :
    Coefficients (fieldBasis s) (SMCombinedCompactAction.field s) := by
  let rg := (DeltaLOneSignedFields.gauge s).comp
    (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup SMCombinedCompactAction.Spin)
  let rs := ((WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)).comp SMMixedCompactWeyl.compact).comp
    (MonoidHom.snd StandardSMGaugeTensor.GaugeGroup SMCombinedCompactAction.Spin)
  let rf := Representation.trivial ℂ SMCombinedCompactAction.Group (ThreeGenerationFermionBound.Flavor s)
  have hg := BasisActionContinuity.comp (gaugeBasis s) (DeltaLOneSignedFields.gauge s) (gauge_coefficients s)
    (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup SMCombinedCompactAction.Spin) continuous_fst
  have hs := BasisActionContinuity.comp (Pi.basisFun ℂ (Fin 2))
    ((WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)).comp SMMixedCompactWeyl.compact)
    (spin_coefficients (DeltaLOneSignedFields.rightHanded s))
    (MonoidHom.snd StandardSMGaugeTensor.GaugeGroup SMCombinedCompactAction.Spin) continuous_snd
  have ht := BasisActionContinuity.tensor (gaugeBasis s) (Pi.basisFun ℂ (Fin 2)) rg rs hg hs
  exact BasisActionContinuity.tensor ((gaugeBasis s).tensorProduct (Pi.basisFun ℂ (Fin 2)))
    (Pi.basisFun ℂ (Fin 3)) (Representation.tprod rg rs) rf ht (BasisActionContinuity.trivial _)



variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

local instance fieldFinite (s : DeltaLOneSignedInput.Species) : FiniteDimensional ℂ
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) := by
  fin_cases s <;> dsimp [DeltaLOneSignedFields.Field,ThreeGenerationFermionBound.Flavor,
    DeltaLOneSignedFields.GaugeCarrier] <;> infer_instance
local instance sourceFinite : FiniteDimensional ℂ
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) := by
  change FiniteDimensional ℂ (LinearMap.range (PatternExteriorSource.map
    (DeltaLOneSignedFields.field flavor) p).toLinearMap)
  infer_instance

def sourceBasis := Module.finBasis ℂ (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p)
abbrev sourceModel := basisCopyRepresentation (sourceBasis flavor p) (SMCombinedCompactAction.source flavor p)

theorem source_continuous : ContinuousRepresentationScope.IsJointlyContinuous (sourceModel flavor p) :=
  BasisActionContinuity.source_copy_continuous SMCombinedCompactAction.field fieldBasis p
    (sourceBasis flavor p) field_coefficients

abbrev weakProjection : SMCombinedCompactAction.Group →* TauCeti.SU2 :=
  (MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp (MonoidHom.fst _ _))
def bosonModel (m : ℕ) (delta : ℤ) : Representation ℂ SMCombinedCompactAction.Group
    (EuclideanSpace ℂ (Fin (m+1))) :=
  charTwist ((SMHiggsConstituents.character (H := H)).comp SMCombinedCompactAction.gaugeEmbedding ^ delta)
    ((TauCeti.SU2.symPowerModel m).toRepresentation.comp weakProjection)

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMCombinedCompactAction.boson (H := H) m delta) (bosonModel (H := H) m delta) where
  toLinearEquiv := TauCeti.SU2.weightEquiv m
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change TauCeti.SU2.weightEquiv m
      (((SMHiggsConstituents.character ^ delta) (SMCombinedCompactAction.gaugeEmbedding g) : ℂˣ) •
        (WeakDoubletScalars.doublet.symmetricPower m) g.1.2.1 x) = _
    rw [Units.smul_def,map_smul,WeakDoubletScalars.symmetricPower_eq]
    exact congrArg (fun y => ((SMHiggsConstituents.character ^ delta)
      (SMCombinedCompactAction.gaugeEmbedding g) : ℂˣ) • y)
      ((TauCeti.SU2.symPowerModelEquiv m).isIntertwining _ _ g.1.2.1 x)

theorem boson_continuous (m : ℕ) (delta : ℤ) : ContinuousRepresentationScope.IsJointlyContinuous
    (bosonModel (H := H) m delta) := by
  apply jointlyContinuous_of_orbit
  intro x
  have hc : Continuous (fun g : SMCombinedCompactAction.Group =>
      (((g.1.2.2 ^ (3 : ℤ)) ^ delta : Circle) : ℂ)) := by
    have hz : Continuous (fun g : SMCombinedCompactAction.Group => g.1.2.2) :=
      continuous_snd.comp (continuous_snd.comp continuous_fst)
    exact continuous_subtype_val.comp ((hz.zpow (3 : ℤ)).zpow delta)
  have hm : Continuous (fun g : SMCombinedCompactAction.Group => TauCeti.SU2.symPowerModel m g.1.2.1 x) :=
    (continuous_clm_apply.mp (TauCeti.SU2.continuous_symPowerModel m) x).comp
      (continuous_fst.comp (continuous_snd.comp continuous_fst))
  have hscalar : Continuous (fun g : SMCombinedCompactAction.Group =>
      ((((SMHiggsConstituents.character (H := H)).comp SMCombinedCompactAction.gaugeEmbedding ^ delta) g : ℂˣ) : ℂ)) := by
    simpa [SMHiggsConstituents.character,SMHiggsConstituents.hyperProjection,
      SMCombinedCompactAction.gaugeEmbedding,SMMixedCompactCoefficients.retained] using hc
  change Continuous (fun g =>
    ((((SMHiggsConstituents.character (H := H)).comp SMCombinedCompactAction.gaugeEmbedding ^ delta) g : ℂˣ) : ℂ) •
      TauCeti.SU2.symPowerModel m g.1.2.1 x)
  exact hscalar.smul hm

abbrev model (m : ℕ) (delta : ℤ) := (sourceModel flavor p).tprod (bosonModel (H := H) m delta)

def equiv (m : ℕ) (delta : ℤ) : Representation.Equiv (SMCombinedCompactAction.action flavor p m delta)
    (model flavor p m delta) :=
  ExternalInvariantTensor.tensorEquiv
    (basisCopyRepresentationEquiv (sourceBasis flavor p) (SMCombinedCompactAction.source flavor p))
    (bosonEquiv (H := H) m delta)

theorem continuous_model (m : ℕ) (delta : ℤ) : ContinuousRepresentationScope.IsJointlyContinuous
    (model flavor p m delta) :=
  jointlyContinuous_tprod _ _ (source_continuous flavor p) (boson_continuous (H := H) m delta)

def coefficientEquiv (m : ℕ) (delta : ℤ) : InvariantCoefficientTransport.Invariants (model flavor p m delta)
    ≃ₗ[ℂ] SMMixedCompactCoefficients.LocalSpace flavor p m delta :=
  (InvariantCoefficientTransport.alongEquiv (equiv flavor p m delta)).symm.trans
    (SMCombinedCompactAction.coefficientEquiv flavor p m delta)

end
end GUT.SMCombinedCompactContinuity
