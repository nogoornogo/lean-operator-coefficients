import Physics.StandardModel.Operators.SMCompactSupportDecision
namespace GUT.SMCompactSupportExamples
open Math
attribute [local instance] SMCompactSupportDecision.higgsDecision

theorem q18Allowed : SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
    (QLFiniteSupport.flavor (0 : ZMod 1) 0) (fun _ : Fin 18 => 0) 0 6) := by
  apply (SMJointHiggsSupport.original_ql_iff (fun _ : Fin 18 => 0) (0 : ZMod 1) 0 0 6).mpr
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel


theorem mixedForbidden : SelectionCriteria.Forbidden (SMFiniteHiggsSupport.OriginalSpace
    (QLFiniteSupport.flavor (0 : ZMod 1) 0) (![0,5] : Fin 2 → DeltaLOneSignedInput.Species) 0 0) := by
  apply (SMJointHiggsSupport.original_ql_forbidden_iff _ (0 : ZMod 1) 0 0 0).mpr
  apply Or.inr
  apply Or.inr
  decide +kernel


end GUT.SMCompactSupportExamples
