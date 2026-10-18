import Physics.StandardModel.Operators.SMJointSpinContent
import Math.RepresentationTheory.SU2IsotypicMatching
import Math.RepresentationTheory.Decomposition.SurjectiveHomTransport

/-! Simultaneous weak/left/right occurrence with the full color/hypercharge
representation retained. All three SU2 equivalence tests are eliminated in
favor of their canonical joint multiplicity representation. -/
namespace GUT.SMJointOccurrence
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor SU2IsotypicEvaluation
open SMJointSpinContent
open scoped TensorProduct

variable {B : Type*} [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
  (c : Representation ℂ ColorHyper B)

abbrev rightTarget (b : ℕ) : Representation ℂ (TauCeti.SU2 × ColorHyper)
    (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B) := external (model b) c
abbrev leftTarget (a b : ℕ) : Representation ℂ (TauCeti.SU2 × LeftRemaining)
    (EuclideanSpace ℂ (Fin (a+1)) ⊗[ℂ] (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B)) :=
  external (model a) ((rightTarget c b).comp rightReorder.toMonoidHom)
abbrev weakTarget (m a b : ℕ) : Representation ℂ (TauCeti.SU2 × SMJointWeakContent.Remaining)
    (EuclideanSpace ℂ (Fin (m+1)) ⊗[ℂ]
      (EuclideanSpace ℂ (Fin (a+1)) ⊗[ℂ] (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B))) :=
  external (model m) ((leftTarget c a b).comp leftReorder.toMonoidHom)
abbrev target (m a b : ℕ) : Representation ℂ SMCombinedCompactAction.Group
    (EuclideanSpace ℂ (Fin (m+1)) ⊗[ℂ]
      (EuclideanSpace ℂ (Fin (a+1)) ⊗[ℂ] (EuclideanSpace ℂ (Fin (b+1)) ⊗[ℂ] B))) :=
  (weakTarget c m a b).comp SMJointWeakContent.reorder.toMonoidHom

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

/-- This is actual joint occurrence for any supplied color/hypercharge
target, without any specieswise-singlet hypothesis or new branching input. -/
theorem hom_allowed_iff (m : Fin (SMContentWeakBound.bound p+1))
    (a : Fin (SMChiralitySupport.count p false+1))
    (b : Fin (SMChiralitySupport.count p true+1)) :
    SelectionCriteria.Allowed (IntertwiningMap (SMCombinedCompactContinuity.sourceModel flavor p)
      (target c m.val a.val b.val)) ↔
      SelectionCriteria.Allowed (IntertwiningMap
        (jointMultiplicity flavor p m.val a.val b.val) c) := by
  have hweak := SelectionCriteria.allowed_equiv
    (SurjectiveHomTransport.homEquiv SMJointWeakContent.reorder.toMonoidHom
      SMJointWeakContent.reorder.surjective (SMJointWeakContent.source flavor p)
      (weakTarget c m.val a.val b.val))
  have hleft := SelectionCriteria.allowed_equiv
    (SurjectiveHomTransport.homEquiv leftReorder.toMonoidHom leftReorder.surjective
      (leftSource flavor p m.val) (leftTarget c a.val b.val))
  have hright := SelectionCriteria.allowed_equiv
    (SurjectiveHomTransport.homEquiv rightReorder.toMonoidHom rightReorder.surjective
      (rightSource flavor p m.val a.val) (rightTarget c b.val))
  exact hweak.trans
    ((SU2IsotypicMatching.ofBound (SMJointWeakContent.source flavor p) (SMContentWeakBound.bound p)
      ((leftTarget c a.val b.val).comp leftReorder.toMonoidHom)
      (SMJointWeakContent.source_continuous flavor p) (SMJointWeakContent.bounded flavor p) m).trans
      (hleft.trans
        ((SU2IsotypicMatching.ofBound (leftSource flavor p m.val) (SMChiralitySupport.count p false)
          ((rightTarget c b.val).comp rightReorder.toMonoidHom)
          (left_continuous flavor p m.val) (left_bounded flavor p m.val) a).trans
          (hright.trans
            (SU2IsotypicMatching.ofBound (rightSource flavor p m.val a.val) (SMChiralitySupport.count p true)
              c (right_continuous flavor p m.val a.val) (right_bounded flavor p m.val a.val) b)))))

end
end GUT.SMJointOccurrence
