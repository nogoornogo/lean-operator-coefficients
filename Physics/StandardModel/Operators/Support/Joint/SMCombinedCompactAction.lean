import Physics.StandardModel.Operators.Support.Joint.SMMixedCompactCoefficients
import Math.RepresentationTheory.Coefficients.ProductInvariantCoefficients

/-! A combined compact local gauge and independent two-chirality action on
actual statistical sources. No compact coefficient comparison is assumed. -/
namespace Physics.SMCombinedCompactAction
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
abbrev Spin := TauCeti.SU2 × TauCeti.SU2
abbrev Group := StandardSMGaugeTensor.GaugeGroup × Spin
abbrev gaugeInclusion : StandardSMGaugeTensor.GaugeGroup →* Group := MonoidHom.inl _ _
abbrev spinInclusion : Spin →* Group := MonoidHom.inr _ _

variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def field (s : DeltaLOneSignedInput.Species) : Representation ℂ Group
    (DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :=
  Representation.tprod
    (Representation.tprod
      ((DeltaLOneSignedFields.gauge s).comp (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup Spin))
      ((WeylIndependentAction.spin (DeltaLOneSignedFields.rightHanded s)).comp
        (SMMixedCompactWeyl.compact.comp (MonoidHom.snd StandardSMGaugeTensor.GaugeGroup Spin))))
    (Representation.trivial ℂ Group (ThreeGenerationFermionBound.Flavor s))

theorem field_gauge (s : DeltaLOneSignedInput.Species) :
    (field s).comp gaugeInclusion = (DeltaLOneSignedFields.field flavor s).comp
      ((SMMixedCompactCoefficients.retained (H := H)).comp (MonoidHom.inl _ _)) := by
  ext g x y z
  simp [field,gaugeInclusion,DeltaLOneSignedFields.field,DeltaLOneSignedFields.localField,
    ExternalInvariantTensor.external,SMMixedCompactCoefficients.retained,Representation.tprod_apply]

theorem field_spin (s : DeltaLOneSignedInput.Species) :
    (field s).comp spinInclusion = (SMMixedCompactWeyl.field s).comp SMMixedCompactWeyl.compact := by
  ext g x y z
  simp [field,spinInclusion,SMMixedCompactWeyl.field,Representation.tprod_apply]

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def source : Representation ℂ Group
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :=
  PatternExteriorSource.representation field p

abbrev gaugeEmbedding : Group →* NeutralHiggsPowers.G H :=
  (SMMixedCompactCoefficients.retained (H := H)).comp
    ((MonoidHom.inl _ _).comp (MonoidHom.fst _ _))

def boson (m : ℕ) (delta : ℤ) : Representation ℂ Group (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
  (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
    SMHiggsConstituents.character m delta).comp (gaugeEmbedding (H := H))

def action (m : ℕ) (delta : ℤ) : Representation ℂ Group (SMFullLocalKernel.Carrier flavor p m) :=
  (source flavor p).tprod (boson (H := H) m delta)

theorem source_gauge : (source flavor p).comp gaugeInclusion =
    (SMFiniteHiggsSupport.source flavor p).comp
      ((SMMixedCompactCoefficients.retained (H := H)).comp (MonoidHom.inl _ _)) := by
  have h₁ := StatisticalSourceRestriction.source field gaugeInclusion
    (fun s => (DeltaLOneSignedFields.field flavor s).comp
      ((SMMixedCompactCoefficients.retained (H := H)).comp (MonoidHom.inl _ _))) p
    (field_gauge flavor)
  have h₂ := StatisticalSourceRestriction.source (DeltaLOneSignedFields.field flavor)
    ((SMMixedCompactCoefficients.retained (H := H)).comp (MonoidHom.inl _ _)) _ p (fun _ => rfl)
  exact h₁.trans h₂.symm

theorem source_spin : (source flavor p).comp spinInclusion =
    (SMMixedCompactWeyl.source flavor p).comp SMMixedCompactWeyl.compact := by
  have h₁ := StatisticalSourceRestriction.source field spinInclusion
    (fun s => (SMMixedCompactWeyl.field s).comp SMMixedCompactWeyl.compact) p field_spin
  have h₂ := StatisticalSourceRestriction.source SMMixedCompactWeyl.field SMMixedCompactWeyl.compact _ p
    (fun _ => rfl)
  exact h₁.trans h₂.symm

theorem action_gauge (m : ℕ) (delta : ℤ) : (action flavor p m delta).comp gaugeInclusion =
    (SMIntegralLocalWeights.action flavor p m delta).comp
      (MonoidHom.inl StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group) := by
  have hs : (source flavor p).comp gaugeInclusion =
      (SMIntegralLocalWeights.source flavor p).comp (MonoidHom.inl _ _) := source_gauge flavor p
  have hb : (boson (H := H) m delta).comp gaugeInclusion =
      (SMIntegralLocalWeights.boson (H := H) m delta).comp (MonoidHom.inl _ _) := by
    ext g : 1
    apply LinearMap.ext
    intro x
    rfl
  let a := (SMIntegralLocalWeights.source flavor p).comp (MonoidHom.inl _ _)
  let b := (SMIntegralLocalWeights.boson (H := H) m delta).comp (MonoidHom.inl _ _)
  have h₁ := StatisticalSourceRestriction.tensor gaugeInclusion (source flavor p)
    (boson (H := H) m delta) a b hs hb
  have h₂ := StatisticalSourceRestriction.tensor
    (MonoidHom.inl StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group)
    (SMIntegralLocalWeights.source flavor p) (SMIntegralLocalWeights.boson (H := H) m delta)
    a b rfl rfl
  exact h₁.trans h₂.symm

theorem action_spin (m : ℕ) (delta : ℤ) : (action flavor p m delta).comp spinInclusion =
    SMMixedCompactCoefficients.compactSpin flavor p m := by
  have hb : (boson (H := H) m delta).comp spinInclusion =
      Representation.trivial ℂ Spin (Sym[ℂ]^m WeakDoubletScalars.Doublet) := by
    ext g : 1
    apply LinearMap.ext
    intro x
    change (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta) 1 x = x
    rw [map_one]; rfl
  let a := (SMMixedCompactWeyl.source flavor p).comp SMMixedCompactWeyl.compact
  let b := Representation.trivial ℂ Spin (Sym[ℂ]^m WeakDoubletScalars.Doublet)
  have h₁ := StatisticalSourceRestriction.tensor spinInclusion (source flavor p)
    (boson (H := H) m delta) a b (source_spin flavor p) hb
  have h₂ := StatisticalSourceRestriction.tensor SMMixedCompactWeyl.compact
    (SMMixedCompactWeyl.source flavor p)
    (Representation.trivial ℂ SMMixedCompactWeyl.Pair (Sym[ℂ]^m WeakDoubletScalars.Doublet)) a b rfl rfl
  exact h₁.trans h₂.symm


def coefficientEquiv (m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants (action flavor p m delta) ≃ₗ[ℂ]
      SMMixedCompactCoefficients.LocalSpace flavor p m delta :=
  ProductInvariantCoefficients.equiv (action flavor p m delta)
    (SMIntegralLocalWeights.action flavor p m delta)
    (MonoidHom.inl StandardSMGaugeTensor.GaugeGroup WeylSpinor.Group)
    (SMMixedCompactCoefficients.compactSpin flavor p m)
    (action_gauge flavor p m delta) (action_spin flavor p m delta)

end
end Physics.SMCombinedCompactAction
