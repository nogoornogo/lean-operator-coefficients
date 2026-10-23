import Physics.StandardModel.Operators.Support.Joint.SMJointWeakContent
import Physics.StandardModel.Operators.Support.Decomposition.SMCompactSpinBound

/-! Iterated complete weak/left/right isotypic decompositions of actual
mixed sources. Each multiplicity retains color and hypercharge; chirality
slot bounds are inherited through invariant ranges, without basis expansion. -/
namespace Physics.SMJointSpinContent
set_option autoImplicit false
noncomputable section
open Math Representation ContinuousRepresentationScope BoundedTorusWeights
open ProductFactorization

abbrev ColorHyper := SMJointWeakContent.Color × Circle
abbrev LeftRemaining := ColorHyper × TauCeti.SU2

local instance remainingMeasurable : MeasurableSpace SMJointWeakContent.Remaining := borel _
local instance remainingBorel : BorelSpace SMJointWeakContent.Remaining := ⟨rfl⟩
local instance leftMeasurable : MeasurableSpace LeftRemaining := borel _
local instance leftBorel : BorelSpace LeftRemaining := ⟨rfl⟩

def leftReorder : SMJointWeakContent.Remaining ≃* (TauCeti.SU2 × LeftRemaining) where
  toFun g := (g.2.1,(g.1,g.2.2))
  invFun g := (g.2.1,(g.1,g.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem left_inverse_continuous : Continuous leftReorder.symm :=
  (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

abbrev rightReorder : LeftRemaining ≃* (TauCeti.SU2 × ColorHyper) := MulEquiv.prodComm

def remainingTorus (side : Bool) : Circle →* SMJointWeakContent.Remaining :=
  (MonoidHom.inr ColorHyper SMCombinedCompactAction.Spin).comp (SMCompactSpinBound.spinTorus side)
def rightTorus : Circle →* LeftRemaining :=
  (MonoidHom.inr ColorHyper TauCeti.SU2).comp TauCeti.SU2.torusHom

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem weak_multiplicity_bounded (m : ℕ) (side : Bool) :
    Bounded (SMJointWeakContent.multiplicity flavor p m) (remainingTorus side)
      (SMChiralitySupport.count p side) := by
  apply SU2IsotypicModels.inherit_bound (SMJointWeakContent.source flavor p) m
    (SMJointWeakContent.source_continuous flavor p)
  exact SMCompactSpinBound.model_bounded flavor p side

abbrev leftSource (m : ℕ) :=
  (SMJointWeakContent.multiplicity flavor p m).comp leftReorder.symm.toMonoidHom

theorem left_continuous (m : ℕ) : IsJointlyContinuous (leftSource flavor p m) :=
  (SMJointWeakContent.multiplicity_continuous flavor p m).comp
    ⟨leftReorder.symm.toMonoidHom,left_inverse_continuous⟩

theorem left_bounded (m : ℕ) : Bounded (firstRestriction (leftSource flavor p m))
    TauCeti.SU2.torusHom (SMChiralitySupport.count p false) :=
  weak_multiplicity_bounded flavor p m false

def leftDecomposition (m : ℕ) : Representation.Equiv
    (FiniteBlockHom.action (SU2IsotypicModels.piece (leftSource flavor p m)
      (SMChiralitySupport.count p false))) (leftSource flavor p m) :=
  SU2IsotypicModels.ofBound (leftSource flavor p m) (SMChiralitySupport.count p false)
    (left_continuous flavor p m) (left_bounded flavor p m)

abbrev LeftMultiplicity (m a : ℕ) := SU2IsotypicModels.Carrier (leftSource flavor p m) a
abbrev leftMultiplicity (m a : ℕ) := SU2IsotypicModels.action (leftSource flavor p m) a

theorem left_multiplicity_continuous (m a : ℕ) : IsJointlyContinuous (leftMultiplicity flavor p m a) :=
  SU2IsotypicModels.continuous_action (leftSource flavor p m) a (left_continuous flavor p m)

theorem right_bounded_in_left (m a : ℕ) : Bounded (leftMultiplicity flavor p m a) rightTorus
    (SMChiralitySupport.count p true) := by
  apply SU2IsotypicModels.inherit_bound (leftSource flavor p m) a (left_continuous flavor p m)
  exact weak_multiplicity_bounded flavor p m true

abbrev rightSource (m a : ℕ) := (leftMultiplicity flavor p m a).comp rightReorder.symm.toMonoidHom

theorem right_continuous (m a : ℕ) : IsJointlyContinuous (rightSource flavor p m a) :=
  (left_multiplicity_continuous flavor p m a).comp ⟨rightReorder.symm.toMonoidHom,continuous_swap⟩

theorem right_bounded (m a : ℕ) : Bounded (firstRestriction (rightSource flavor p m a))
    TauCeti.SU2.torusHom (SMChiralitySupport.count p true) :=
  right_bounded_in_left flavor p m a

def rightDecomposition (m a : ℕ) : Representation.Equiv
    (FiniteBlockHom.action (SU2IsotypicModels.piece (rightSource flavor p m a)
      (SMChiralitySupport.count p true))) (rightSource flavor p m a) :=
  SU2IsotypicModels.ofBound (rightSource flavor p m a) (SMChiralitySupport.count p true)
    (right_continuous flavor p m a) (right_bounded flavor p m a)

/-- The three labels are weak, left spin and right spin. This carrier still
has its complete color/hypercharge action; nonzeroness is not assumed. -/
abbrev JointMultiplicity (m a b : ℕ) := SU2IsotypicModels.Carrier (rightSource flavor p m a) b
abbrev jointMultiplicity (m a b : ℕ) := SU2IsotypicModels.action (rightSource flavor p m a) b

theorem joint_continuous (m a b : ℕ) : IsJointlyContinuous (jointMultiplicity flavor p m a b) :=
  SU2IsotypicModels.continuous_action (rightSource flavor p m a) b (right_continuous flavor p m a)

end
end Physics.SMJointSpinContent
