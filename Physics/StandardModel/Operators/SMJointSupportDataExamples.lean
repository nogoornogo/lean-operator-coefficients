import Physics.StandardModel.Operators.SMJointSupportData
import Physics.StandardModel.Operators.SMMixedFamilySupport
import Physics.StandardModel.Operators.SMChiralitySupport

/-! Downstream consumers using ordinary lemmas and explicit source/Higgs
choices. No numerical table, decision procedure or automatic witness search. -/
namespace GUT.SMJointSupportDataExamples
set_option autoImplicit false
open Math

/-- Generic use stays abstract in content, spin degree and the chosen component. -/
theorem component_to_support (c : DeltaLOneSignedInput.Species → Nat) (m : Nat)
    (o : SMJointSupportData.Index c)
    (b : JointSourceExpression.Choice (SMJointSupportData.expressionData c m o))
    (hb : JointColorSpinWord.Supports (JointSourceExpression.word
      (SMJointSupportData.expressionData c m o) b)) :
    SMJointContentSupport.Supports c m :=
  SMJointSupportData.witness_to_original c m o ⟨b,hb⟩

/-- A provided data witness transports to the actual original space, uniformly. -/
theorem original_of_data {k : Nat} [NeZero k] (q l : ZMod k) {n : Nat}
    (p : Fin n → DeltaLOneSignedInput.Species) (h d : Nat)
    (hc : QLFiniteSupport.charge q l p=0)
    (hy : SMContentWeakBound.hypercharge p+3*((h : Int)-d)=0)
    (hs : SMJointSupportData.HiggsDataSupport p h d) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) :=
  (SMJointSupportData.original_ql_iff q l p h d).mpr ⟨hc,hy,hs⟩

/-- The explicit mixed source is d,u,Q,L, with no Higgs factors. -/
abbrev mixedPattern := SMMixedFamilySupport.pattern 0

theorem mixed_allowed : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (0 : ZMod 1) 0) mixedPattern 0 0) := by
  apply (SMMixedFamilySupport.original_ql_iff (0 : ZMod 1) 0 0 0 0).mpr
  exact ⟨rfl, by simp only [mul_zero,add_zero]⟩

theorem mixed_data_witness : SMJointSupportData.HiggsDataSupport mixedPattern 0 0 :=
  ((SMJointSupportData.original_ql_iff (0 : ZMod 1) 0 mixedPattern 0 0).mp mixed_allowed).2.2

abbrev q18Pattern := SMConstantWeakCapacity.pattern 0 18

theorem q18_allowed : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (0 : ZMod 1) 0) q18Pattern 0 6) := by
  apply (SMLowerHiggsSupport.quark_ql_iff (0 : ZMod 1) 0 18 (Or.inr (Or.inr rfl)) 0 6).mpr
  constructor
  · rw [SMLowerHiggsSupport.quark_residual_charge]
    exact nsmul_zero 18
  · change (3 : Int)*6 + 3*(0-6)=0
    rw [zero_sub,mul_neg,add_neg_cancel]

theorem q18_data_witness : SMJointSupportData.HiggsDataSupport q18Pattern 0 6 :=
  ((SMJointSupportData.original_ql_iff (0 : ZMod 1) 0 q18Pattern 0 6).mp q18_allowed).2.2

def oppositePair : Fin 2 → DeltaLOneSignedInput.Species := ![0,5]

theorem oppositePair_forbidden {k : Nat} [NeZero k] (q l : ZMod k) (h d : Nat) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) oppositePair h d) := by
  apply SMChiralitySupport.original_forbidden _ oppositePair true ?_ h d
  change 1 ≠ 0
  exact Nat.one_ne_zero

theorem oppositePair_no_data : ¬ SMJointSupportData.HiggsDataSupport oppositePair 0 0 := by
  intro hs
  have ha := original_of_data (0 : ZMod 1) 0 oppositePair 0 0
    (by simp [QLFiniteSupport.charge, DuqlHiggsContent.signedCharge, oppositePair, Fin.sum_univ_succ])
    (by rfl) hs
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp (oppositePair_forbidden 0 0 0 0) ha

end GUT.SMJointSupportDataExamples
