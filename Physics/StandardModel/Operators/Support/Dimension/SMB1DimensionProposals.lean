import Physics.StandardModel.Operators.Support.Dimension.SMMinimumOperatorDimension
-- Elaborate the finite certificates sequentially within this module.
set_option Elab.async false

namespace Physics.SMB1DimensionProposals
open Math Physics
attribute [local instance] SMCompactSupportDecision.expressionDecision
attribute [local instance] SMCompactSupportDecision.jointDecision
def p5Counts : DeltaLOneSignedInput.Species → Nat := ![0,3,0,4,1,0,0,0,0,0]
def p5Pattern : Fin 8 → DeltaLOneSignedInput.Species := ![1,1,1,3,3,3,3,4]
theorem p5_counts : SMIteratedContent.counts p5Pattern=p5Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem p5_support : SMJointContentSupport.Supports p5Counts 2 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced p5Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def n5Counts : DeltaLOneSignedInput.Species → Nat := ![0,0,3,0,0,0,0,0,5,0]
def n5Pattern : Fin 8 → DeltaLOneSignedInput.Species := ![2,2,2,8,8,8,8,8]
theorem n5_counts : SMIteratedContent.counts n5Pattern=n5Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem n5_support : SMJointContentSupport.Supports n5Counts 3 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced n5Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def p7Counts : DeltaLOneSignedInput.Species → Nat := ![0,3,0,6,1,0,0,0,0,0]
def p7Pattern : Fin 10 → DeltaLOneSignedInput.Species := ![1,1,1,3,3,3,3,3,3,4]
theorem p7_counts : SMIteratedContent.counts p7Pattern=p7Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem p7_support : SMJointContentSupport.Supports p7Counts 4 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced p7Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def n7Counts : DeltaLOneSignedInput.Species → Nat := ![0,0,3,0,0,0,0,0,7,0]
def n7Pattern : Fin 10 → DeltaLOneSignedInput.Species := ![2,2,2,8,8,8,8,8,8,8]
theorem n7_counts : SMIteratedContent.counts n7Pattern=n7Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem n7_support : SMJointContentSupport.Supports n7Counts 5 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced n7Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def p9Counts : DeltaLOneSignedInput.Species → Nat := ![0,4,0,9,0,0,0,1,0,0]
def p9Pattern : Fin 14 → DeltaLOneSignedInput.Species := ![1,1,1,1,3,3,3,3,3,3,3,3,3,7]
theorem p9_counts : SMIteratedContent.counts p9Pattern=p9Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem p9_support : SMJointContentSupport.Supports p9Counts 3 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced p9Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def n9Counts : DeltaLOneSignedInput.Species → Nat := ![0,0,5,0,0,0,2,0,9,0]
def n9Pattern : Fin 16 → DeltaLOneSignedInput.Species := ![2,2,2,2,2,6,6,8,8,8,8,8,8,8,8,8]
theorem n9_counts : SMIteratedContent.counts n9Pattern=n9Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem n9_support : SMJointContentSupport.Supports n9Counts 3 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced n9Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def p11Counts : DeltaLOneSignedInput.Species → Nat := ![0,6,0,11,0,0,0,3,0,0]
def p11Pattern : Fin 20 → DeltaLOneSignedInput.Species := ![1,1,1,1,1,1,3,3,3,3,3,3,3,3,3,3,3,7,7,7]
theorem p11_counts : SMIteratedContent.counts p11Pattern=p11Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem p11_support : SMJointContentSupport.Supports p11Counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced p11Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
def n11Counts : DeltaLOneSignedInput.Species → Nat := ![0,0,7,0,0,0,4,0,11,0]
def n11Pattern : Fin 22 → DeltaLOneSignedInput.Species := ![2,2,2,2,2,2,2,6,6,6,6,8,8,8,8,8,8,8,8,8,8,8]
theorem n11_counts : SMIteratedContent.counts n11Pattern=n11Counts := by
  funext t
  fin_cases t <;> decide +kernel
theorem n11_support : SMJointContentSupport.Supports n11Counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced n11Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel
end Physics.SMB1DimensionProposals
