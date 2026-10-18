import Math.RepresentationTheory.CompactGenerationOccupations
import Physics.StandardModel.Operators.SMJointHiggsSupport

/-! Opt-in finite decisions preserving the existing structural support predicates.
No global instance replaces the default enumeration. -/
namespace GUT.SMCompactSupportDecision
set_option autoImplicit false
open Math

local instance su2Decision (w : SU2TensorWordSupport.Word) :
    Decidable (SU2TensorWordSupport.Supports w) := by
  unfold SU2TensorWordSupport.Supports
  infer_instance
local instance ownerEq : (w : ColorTensorTree.Shape) → DecidableEq (ColorTensorTree.Leaf w)
  | .leaf _ _ => inferInstanceAs (DecidableEq Unit)
  | .tensor l r => by
    letI := ownerEq l
    letI := ownerEq r
    exact inferInstanceAs (DecidableEq (ColorTensorTree.Leaf l ⊕ ColorTensorTree.Leaf r))
local instance positiveDecision (w : ColorTensorTree.Shape) (k : Nat)
    (h : ColorTensorTree.positive w = ColorTensorTree.negative w + 3*k)
    (s : Equiv.Perm (Fin (ColorTensorTree.negative w + 3*k))) :
    Decidable (ColorTreeDiagrams.PositiveValid w k h s) := by
  unfold ColorTreeDiagrams.PositiveValid Function.Injective
  infer_instance
local instance negativeDecision (w : ColorTensorTree.Shape) (k : Nat)
    (h : ColorTensorTree.negative w = ColorTensorTree.positive w + 3*k)
    (s : Equiv.Perm (Fin (ColorTensorTree.positive w + 3*k))) :
    Decidable (ColorTreeDiagrams.NegativeValid w k h s) := by
  unfold ColorTreeDiagrams.NegativeValid Function.Injective
  infer_instance
local instance diagramDecision (t : ColorFlagTree.Tree) : Decidable (ColorTreeSupport.DiagramSupport t) := by
  unfold ColorTreeSupport.DiagramSupport
  infer_instance
noncomputable local instance colorDecision (w : RestrictedColorWordSupport.Word) :
    Decidable (RestrictedColorWordSupport.Supports w) := by
  unfold RestrictedColorWordSupport.Supports
  infer_instance
noncomputable local instance jointDecision (w : JointColorSpinWord.Word) : Decidable (JointColorSpinWord.Supports w) := by
  unfold JointColorSpinWord.Supports
  infer_instance
noncomputable local instance expressionDecision (e : JointSourceExpression.Expr) : Decidable (JointSourceExpression.Supports e) := by
  unfold JointSourceExpression.Supports
  infer_instance

/-- Same support proposition, with compact enumeration selected at every leaf. -/
@[instance_reducible]
noncomputable def contentDecision (c : DeltaLOneSignedInput.Species → ℕ) (m : ℕ) :
    Decidable (SMJointContentSupport.Supports c m) := by
  letI := Math.CompactGenerationOccupations.choiceFintype (SMJointContentSupport.tree c)
  unfold SMJointContentSupport.Supports JointContentPresentation.Supports
  infer_instance
attribute [local instance] contentDecision

/-- Opt-in closed-kernel decision. Noncomputable presentation dependencies remain. -/
@[instance_reducible]
noncomputable def higgsDecision {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ) :
    Decidable (SMJointHiggsSupport.HiggsSupport p h d) := by
  unfold SMJointHiggsSupport.HiggsSupport BoundedHiggsSupport.Admissible
  infer_instance

end GUT.SMCompactSupportDecision
