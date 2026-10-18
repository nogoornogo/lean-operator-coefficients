import Physics.StandardModel.Operators.SMJointOccurrence
import Math.RepresentationTheory.SU2FiniteCoupling
import Math.RepresentationTheory.CharacterTwistTransport

/-! The actual Higgs coefficient selects weak m and both spin labels zero.
All actions and tensor factors are transported explicitly; the remaining
color/hypercharge Hom is the joint multiplicity, not a single-species test. -/
namespace GUT.SMJointCoefficient
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor SU2IsotypicEvaluation
open SMJointSpinContent SMJointOccurrence
open scoped TensorProduct

def colorHyperProjection : SMCombinedCompactAction.Group →* ColorHyper where
  toFun g := (g.1.1,g.1.2.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def character (delta : ℤ) : ColorHyper →* ℂˣ :=
  (Circle.toUnits.comp (MonoidHom.snd SMJointWeakContent.Color Circle)) ^ (-(3*delta))
def line (delta : ℤ) : Representation ℂ ColorHyper ℂ := ofLinearCharacter (character delta)

def collapsedSpin {B : Type*} [AddCommGroup B] [Module ℂ B]
    (c : Representation ℂ ColorHyper B) : Representation.Equiv
      ((leftTarget c 0 0).comp leftReorder.toMonoidHom)
      (c.comp (MonoidHom.fst ColorHyper SMCombinedCompactAction.Spin)) :=
  SplitRepresentationProjection.restrictEquiv
    ((externalEquiv (Representation.Equiv.refl (model 0))
      (SplitRepresentationProjection.restrictEquiv (SU2IsotypicMatching.zeroFactor c)
        rightReorder.toMonoidHom)).trans
      (SU2IsotypicMatching.zeroFactor (c.comp (MonoidHom.fst ColorHyper TauCeti.SU2))))
    leftReorder.toMonoidHom

def collapsedTarget {B : Type*} [AddCommGroup B] [Module ℂ B]
    (c : Representation ℂ ColorHyper B) (m : ℕ) : Representation.Equiv (target c m 0 0)
      ((external (model m) (c.comp (MonoidHom.fst ColorHyper SMCombinedCompactAction.Spin))).comp
        SMJointWeakContent.reorder.toMonoidHom) :=
  SplitRepresentationProjection.restrictEquiv
    (externalEquiv (Representation.Equiv.refl (model m)) (collapsedSpin c))
    SMJointWeakContent.reorder.toMonoidHom

variable {H : Type*} [Group H]

abbrev phase (delta : ℤ) :=
  ((SMHiggsConstituents.character (H := H)).comp SMCombinedCompactAction.gaugeEmbedding) ^ delta
abbrev weakModel (m : ℕ) : Representation ℂ SMCombinedCompactAction.Group
    (EuclideanSpace ℂ (Fin (m+1))) :=
  (model m).comp SMCombinedCompactContinuity.weakProjection

theorem character_eq (delta : ℤ) : (character delta).comp colorHyperProjection =
    (phase (H := H) delta)⁻¹ := by
  apply MonoidHom.ext
  intro g
  change (Circle.toUnits g.1.2.2)^(-(3*delta)) =
    ((Circle.toUnits (g.1.2.2^(3 : ℤ)))^delta)⁻¹
  rw [map_zpow,← zpow_mul,zpow_neg]

def weakSelfDual (m : ℕ) : Representation.Equiv (weakModel m) (weakModel m).dual := by
  let e := TauCeti.SU2.symPowerModelEquiv m
  let s₀ : Representation.Equiv (TauCeti.SU2.symPower m) (TauCeti.SU2.symPower m).dual := by
    rw [← WeakDoubletScalars.symmetricPower_eq]
    exact SU2FiniteCoupling.selfDual m
  let s : Representation.Equiv (model m) (model m).dual :=
    e.symm.trans (s₀.trans (SplitRepresentationProjection.dualEquiv e))
  have h := SplitRepresentationProjection.restrictEquiv s SMCombinedCompactContinuity.weakProjection
  rw [SplitRepresentationProjection.dual_comp] at h
  exact h

def inverseBoson (m : ℕ) (delta : ℤ) : Representation.Equiv
    (charTwist (phase (H := H) delta)⁻¹ (weakModel m))
    (SMCombinedCompactContinuity.bosonModel (H := H) m delta).dual :=
  (CharacterTwistTransport.alongEquiv (phase (H := H) delta)⁻¹ (weakSelfDual m)).trans
    (CharacterTwistTransport.dual (phase (H := H) delta) (weakModel m)).symm

def targetEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (target (line delta) m 0 0) (SMCombinedCompactContinuity.bosonModel (H := H) m delta).dual := by
  refine (collapsedTarget (line delta) m).trans ?_
  change Representation.Equiv
    ((weakModel m).tprod (ofLinearCharacter ((character delta).comp colorHyperProjection))) _
  refine (Representation.tprodOfLinearCharacterEquivCharTwist _ _).trans ?_
  rw [character_eq (H := H)]
  exact inverseBoson (H := H) m delta

variable (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem local_allowed_iff (m : Fin (SMContentWeakBound.bound p+1)) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m.val delta)) ↔
      SelectionCriteria.Allowed (IntertwiningMap (jointMultiplicity flavor p m.val 0 0) (line delta)) := by
  have he := SelectionCriteria.allowed_equiv
    ((SMMixedCompactCoefficients.localEquiv flavor p m.val delta).trans
      (SMCombinedCompactContinuity.coefficientEquiv flavor p m.val delta).symm)
  refine he.trans ((SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv
    (SMCombinedCompactContinuity.sourceModel flavor p)
    (SMCombinedCompactContinuity.bosonModel (H := H) m.val delta))).trans ?_)
  refine (SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv
    (Representation.Equiv.refl _) (targetEquiv (H := H) m.val delta).symm)).trans ?_
  exact SMJointOccurrence.hom_allowed_iff (line delta) flavor p m 0 0

end
end GUT.SMJointCoefficient
