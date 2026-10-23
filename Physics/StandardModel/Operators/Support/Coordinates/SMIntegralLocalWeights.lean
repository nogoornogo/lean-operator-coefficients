import Physics.StandardModel.Operators.Support.Quark.SMColorIntegralBasis
import Physics.StandardModel.Operators.Support.Coordinates.SMWeylFiniteKernel

/-! Actual integral torus spanning for full local statistical source/Higgs actions. -/
namespace Physics.SMIntegralLocalWeights
set_option autoImplicit false
noncomputable section
open Math Representation IntegralTorusTests
open scoped TensorProduct
abbrev Group := StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group

def color : ColorPlaneCircles.SU3 →* Group where
  toFun g := ((g,(1,1)),1)
  map_one' := rfl
  map_mul' _ _ := by simp

def weak : TwoCircleGeneration.SU2 →* Group where
  toFun g := ((1,(g,1)),1)
  map_one' := rfl
  map_mul' _ _ := by simp

def hyper : Circle →* Group where
  toFun z := ((1,(1,z)),1)
  map_one' := rfl
  map_mul' _ _ := by simp

def spin : WeylSpinor.Group →* Group := MonoidHom.inr _ _
def colorTorus : Circle →* Group := color.comp ColorPlaneCircles.torus
def weakTorus : Circle →* Group := weak.comp TauCeti.SU2.torusHom

variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev source : Representation ℂ Group
    (PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :=
  (SMContentWeakBound.source flavor p).comp (MonoidHom.inl Group H)
abbrev boson (m : ℕ) (delta : ℤ) :
    Representation ℂ Group (Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
  (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
    SMHiggsConstituents.character m delta).comp (MonoidHom.inl Group H)
abbrev action (m : ℕ) (delta : ℤ) : Representation ℂ Group
    ((PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) ⊗[ℂ]
      Sym[ℂ]^m WeakDoubletScalars.Doublet) :=
  (source flavor p).tprod (boson (H := H) m delta)

theorem source_color : Integral (source flavor p) colorTorus :=
  SMColorIntegralBasis.source_integral flavor p

theorem source_weak : Integral (source flavor p) weakTorus :=
  IntegralTorusTests.of_bounded (SMContentWeakBound.source flavor p)
    (SMWeakWeightBasis.fullTorus (H := H)) (SMContentWeakBound.bound p)
    (SMContentWeakBound.source_bounded flavor p)

theorem source_hyper : Integral (source flavor p) hyper :=
  scalar (source flavor p) hyper (SMContentWeakBound.hypercharge p)
    (SMContentWeakBound.source_hypercharge flavor p)

theorem boson_color (m : ℕ) (delta : ℤ) : Integral (boson (H := H) m delta) colorTorus := by
  apply scalar _ _ 0
  intro z x
  have hc : SMHiggsConstituents.character (H := H) (colorTorus z,1) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply,colorTorus,color,StandardSMGaugeTensor.phase]
  change ((SMHiggsConstituents.character^delta) (colorTorus z,1) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) 1 x = (z : ℂ)^0 • x
  simp [hc]

theorem boson_weak (m : ℕ) (delta : ℤ) : Integral (boson (H := H) m delta) weakTorus := by
  apply IntegralTorusTests.of_basis _ _ (TauCeti.SU2.weightBasis m) (TauCeti.SU2.weight m)
  intro i z
  have hc : SMHiggsConstituents.character (H := H) (weakTorus z,1) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply,weakTorus,weak,StandardSMGaugeTensor.phase]
  have hp : (SMHiggsConstituents.character (H := H)^delta) (weakTorus z,1) = 1 := by
    rw [MonoidHom.zpow_apply, hc, one_zpow]
  change ((SMHiggsConstituents.character^delta) (weakTorus z,1) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) (TauCeti.SU2.torusHom z)
      (TauCeti.SU2.weightBasis m i) = _
  rw [hp, one_smul]
  rw [WeakDoubletScalars.symmetricPower_eq,
    TauCeti.SU2.symPower_torusHom_weightBasis]

theorem boson_hyper (m : ℕ) (delta : ℤ) : Integral (boson (H := H) m delta) hyper := by
  apply scalar _ _ (3*delta)
  intro z x
  change ((SMHiggsConstituents.character^delta) (hyper z,1) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) 1 x = _
  have hc : (SMHiggsConstituents.character (H := H) (hyper z,1) : ℂ) = (z : ℂ)^3 := by
    rfl
  simp only [map_one,Module.End.one_apply]
  have hp : (((SMHiggsConstituents.character (H := H)^delta) (hyper z,1) : ℂˣ) : ℂ) =
      (z : ℂ)^(3*delta) := by
    change ((SMHiggsConstituents.character (H := H) (hyper z,1) : ℂˣ)^delta : ℂˣ).val = _
    rw [Units.val_zpow_eq_zpow_val,hc]
    simpa [zpow_ofNat] using (zpow_mul (z : ℂ) (3 : ℤ) delta).symm
  exact congrArg (fun c : ℂ => c • x) hp

theorem action_color (m : ℕ) (delta : ℤ) : Integral (action flavor p m delta) colorTorus :=
  tensor (source flavor p) colorTorus (boson (H := H) m delta)
    (source_color flavor p) (boson_color m delta)

theorem action_weak (m : ℕ) (delta : ℤ) : Integral (action flavor p m delta) weakTorus :=
  tensor (source flavor p) weakTorus (boson (H := H) m delta)
    (source_weak flavor p) (boson_weak m delta)

theorem action_hyper (m : ℕ) (delta : ℤ) : Integral (action flavor p m delta) hyper :=
  tensor (source flavor p) hyper (boson (H := H) m delta)
    (source_hyper flavor p) (boson_hyper m delta)

end
end Physics.SMIntegralLocalWeights
