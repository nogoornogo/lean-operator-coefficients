import Math.RepresentationTheory.Content.JointContentPresentation
import Physics.StandardModel.Operators.Support.Joint.SMSignedCoreJointPresentation
import Physics.StandardModel.Operators.Support.Coordinates.SMIteratedContent
import Physics.StandardModel.Operators.Support.Decomposition.SMGenerationCoefficients

/-! Actual complete ten-species, three-generation semisimple support.
Only finite occupation choices, positive color diagrams and three SU2
coupling paths remain. No multiplicity, rank or source-comparison input. -/
namespace Physics.SMJointContentSupport
set_option autoImplicit false
noncomputable section
open Math Representation ExteriorContentTree JointSourcePresentation
open scoped TensorProduct

def leaves (c : DeltaLOneSignedInput.Species → ℕ) (s : DeltaLOneSignedInput.Species) :
    Leaf SMGenerationCauchy.Group where
  Carrier := SMGenerationExhaustion.Core s
  rho := SMColoredCoreBranching.core s
  degree := c s

abbrev tree (c : DeltaLOneSignedInput.Species → ℕ) := IndexedExteriorContent.tree 9 (leaves c)

def cores (c : DeltaLOneSignedInput.Species → ℕ) : JointContentPresentation.Cores (tree c) :=
  JointContentPresentation.indexedCores 9 (leaves c) SMSignedCoreJointPresentation.presentation

def Supports (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) : Prop :=
  JointContentPresentation.Supports (tree c) (cores c) (SMQJointPresentation.weak m)

/-- The expression is metadata from proved core decompositions. Its branch
choices do not contain a supplied Hom, rank or source-matching condition. -/
def expression (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ)
    (o : GenerationTensorSupport.Choice (tree c)) : JointSourceExpression.Expr :=
  (tensor (JointContentPresentation.occupied (tree c) (cores c) o)
    (SMQJointPresentation.weak m)).expression

theorem supports_iff_choices (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) :
    Supports c m ↔ ∃ o : GenerationTensorSupport.Choice (tree c),
      ∃ b : JointSourceExpression.Choice (expression c m o),
        JointColorSpinWord.Supports (JointSourceExpression.word (expression c m o) b) := Iff.rfl

theorem field_restrict (s : DeltaLOneSignedInput.Species) :
    (SMCombinedCompactAction.field s).comp SMGenerationCauchy.inclusion =
      GenerationExteriorExhaustion.generations (SMColoredCoreBranching.core s) := by
  ext g x y z
  rfl

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem source_restrict :
    (SMCombinedCompactAction.source flavor p).comp SMGenerationCauchy.inclusion =
    PatternExteriorSource.representation
      (fun s => GenerationExteriorExhaustion.generations (SMColoredCoreBranching.core s)) p :=
  StatisticalSourceRestriction.source SMCombinedCompactAction.field SMGenerationCauchy.inclusion
    _ p field_restrict

def sourceEquiv : Representation.Equiv
    (factor (GenerationTensorSupport.generations (tree (SMIteratedContent.counts p))))
    ((SMCombinedCompactAction.source flavor p).comp SMGenerationCauchy.inclusion) :=
  (GenerationTensorSupport.indexedDecomposition 9 (leaves (SMIteratedContent.counts p)) p
    (fun _ => rfl)).trans
      (GenerationTensorSupport.equivOfEq (source_restrict flavor p).symm)

def actionEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    ((factor (GenerationTensorSupport.generations (tree (SMIteratedContent.counts p)))).tprod
      (SMGenerationCauchy.weak.symmetricPower m))
    ((SMCombinedCompactAction.action flavor p m delta).comp SMGenerationCauchy.inclusion) :=
  (ExternalInvariantTensor.tensorEquiv (sourceEquiv flavor p) (.refl _)).trans
    (SMGenerationCoefficients.actionEquiv flavor p m delta)

theorem restricted_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((SMCombinedCompactAction.action flavor p m delta).comp SMGenerationCauchy.inclusion)) ↔
    Supports (SMIteratedContent.counts p) m :=
  (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
    (actionEquiv flavor p m delta))).symm.trans
      (JointContentPresentation.allowed_iff _ (cores _) (SMQJointPresentation.weak m))

end
end Physics.SMJointContentSupport
