import Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionBounds
import Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionProposals

/-! Graded actual coefficient witnesses, not ungraded existence assertions. -/
-- Elaborate the finite certificates sequentially within this module.
set_option Elab.async false

namespace Physics.SMB1DimensionWitnesses
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds

def Attains {k : ℕ} [NeZero k] (q l : ZMod k) (L : ℤ) (M : ℕ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → Species) (h d : ℕ),
    SMQLPatternRequests.blCharge p=(3,L) ∧
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ∧
    twiceDimension n h d=M

theorem n17_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-17 : ZMod k)*l=0) : Attains q l (-17) 122 := by
  refine ⟨40,SMLeptonChargeWitnesses.w3_n17_pattern,0,1,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_n17_pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_n17_pattern=(3,-17) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_n17_counts_eq]
    exact SMLeptonChargeWitnesses.w3_n17_support

theorem n15_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-15 : ZMod k)*l=0) : Attains q l (-15) 104 := by
  refine ⟨34,SMLeptonChargeWitnesses.w3_n15_pattern,0,1,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_n15_pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_n15_pattern=(3,-15) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_n15_counts_eq]
    exact SMLeptonChargeWitnesses.w3_n15_support

theorem n13_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-13 : ZMod k)*l=0) : Attains q l (-13) 86 := by
  refine ⟨28,SMLeptonChargeWitnesses.w3_n13_pattern,0,1,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_n13_pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_n13_pattern=(3,-13) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_n13_counts_eq]
    exact SMLeptonChargeWitnesses.w3_n13_support

theorem n11_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-11 : ZMod k)*l=0) : Attains q l (-11) 68 := by
  refine ⟨22,SMB1DimensionProposals.n11Pattern,0,1,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.n11Pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.n11Pattern=(3,-11) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.n11_counts]
    exact SMB1DimensionProposals.n11_support

theorem n9_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-9 : ZMod k)*l=0) : Attains q l (-9) 54 := by
  refine ⟨16,SMB1DimensionProposals.n9Pattern,0,3,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.n9Pattern q l 0 3).mpr
  refine ⟨?_,by decide +kernel,⟨⟨3,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.n9Pattern=(3,-9) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 3 3
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.n9_counts]
    exact SMB1DimensionProposals.n9_support

theorem n7_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-7 : ZMod k)*l=0) : Attains q l (-7) 40 := by
  refine ⟨10,SMB1DimensionProposals.n7Pattern,0,5,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.n7Pattern q l 0 5).mpr
  refine ⟨?_,by decide +kernel,⟨⟨5,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.n7Pattern=(3,-7) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 5 5
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.n7_counts]
    exact SMB1DimensionProposals.n7_support

theorem n5_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-5 : ZMod k)*l=0) : Attains q l (-5) 30 := by
  refine ⟨8,SMB1DimensionProposals.n5Pattern,0,3,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.n5Pattern q l 0 3).mpr
  refine ⟨?_,by decide +kernel,⟨⟨3,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.n5Pattern=(3,-5) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 3 3
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.n5_counts]
    exact SMB1DimensionProposals.n5_support

theorem n3_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-3 : ZMod k)*l=0) : Attains q l (-3) 20 := by
  refine ⟨6,SMMinimumOperatorDimension.h2Pattern,0,1,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMMinimumOperatorDimension.h2Pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMMinimumOperatorDimension.h2Pattern=(3,-3) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMMinimumOperatorDimension.h2_counts]
    exact SMMinimumOperatorDimension.h2_support

theorem n1_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(-1 : ZMod k)*l=0) : Attains q l (-1) 14 := by
  refine ⟨4,SMLeptonChargeWitnesses.w3_n1_pattern,0,1,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_n1_pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_n1_pattern=(3,-1) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_n1_counts_eq]
    exact SMLeptonChargeWitnesses.w3_n1_support

theorem p1_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(1 : ZMod k)*l=0) : Attains q l 1 12 := by
  refine ⟨4,SMMinimumOperatorDimension.c1Pattern,0,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMMinimumOperatorDimension.c1Pattern q l 0 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨0,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMMinimumOperatorDimension.c1Pattern=(3,1) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMMinimumOperatorDimension.c1_counts]
    exact SMMinimumOperatorDimension.c1_support

theorem p3_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(3 : ZMod k)*l=0) : Attains q l 3 18 := by
  refine ⟨6,SMMinimumOperatorDimension.h1Pattern,0,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMMinimumOperatorDimension.h1Pattern q l 0 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨0,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMMinimumOperatorDimension.h1Pattern=(3,3) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMMinimumOperatorDimension.h1_counts]
    exact SMMinimumOperatorDimension.h1_support

theorem p5_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(5 : ZMod k)*l=0) : Attains q l 5 28 := by
  refine ⟨8,SMB1DimensionProposals.p5Pattern,2,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.p5Pattern q l 2 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨2,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.p5Pattern=(3,5) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 2 0 2
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.p5_counts]
    exact SMB1DimensionProposals.p5_support

theorem p7_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(7 : ZMod k)*l=0) : Attains q l 7 38 := by
  refine ⟨10,SMB1DimensionProposals.p7Pattern,4,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.p7Pattern q l 4 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨4,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.p7Pattern=(3,7) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 4 0 4
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.p7_counts]
    exact SMB1DimensionProposals.p7_support

theorem p9_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(9 : ZMod k)*l=0) : Attains q l 9 48 := by
  refine ⟨14,SMB1DimensionProposals.p9Pattern,3,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.p9Pattern q l 3 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨3,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.p9Pattern=(3,9) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 3 0 3
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.p9_counts]
    exact SMB1DimensionProposals.p9_support

theorem p11_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(11 : ZMod k)*l=0) : Attains q l 11 62 := by
  refine ⟨20,SMB1DimensionProposals.p11Pattern,1,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMB1DimensionProposals.p11Pattern q l 1 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMB1DimensionProposals.p11Pattern=(3,11) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMB1DimensionProposals.p11_counts]
    exact SMB1DimensionProposals.p11_support

theorem p13_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(13 : ZMod k)*l=0) : Attains q l 13 80 := by
  refine ⟨26,SMLeptonChargeWitnesses.w3_p13_pattern,1,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_p13_pattern q l 1 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_p13_pattern=(3,13) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_p13_counts_eq]
    exact SMLeptonChargeWitnesses.w3_p13_support

theorem p15_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(15 : ZMod k)*l=0) : Attains q l 15 98 := by
  refine ⟨32,SMLeptonChargeWitnesses.w3_p15_pattern,1,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_p15_pattern q l 1 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_p15_pattern=(3,15) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_p15_counts_eq]
    exact SMLeptonChargeWitnesses.w3_p15_support

theorem p17_attains {k : ℕ} [NeZero k] (q l : ZMod k)
    (hc : (3 : ZMod k)*q+(17 : ZMod k)*l=0) : Attains q l 17 116 := by
  refine ⟨38,SMLeptonChargeWitnesses.w3_p17_pattern,1,0,by decide +kernel,?_,rfl⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_p17_pattern q l 1 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_p17_pattern=(3,17) := by decide +kernel
    rw [he]
    simpa using hc
  · change BoundedHiggsSupport.Admissible 1 0 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_p17_counts_eq]
    exact SMLeptonChargeWitnesses.w3_p17_support

def upperGrade (L : ℤ) : ℕ :=
  if L=-17 then 122 else
  if L=-15 then 104 else
  if L=-13 then 86 else
  if L=-11 then 68 else
  if L=-9 then 54 else
  if L=-7 then 40 else
  if L=-5 then 30 else
  if L=-3 then 20 else
  if L=-1 then 14 else
  if L=1 then 12 else
  if L=3 then 18 else
  if L=5 then 28 else
  if L=7 then 38 else
  if L=9 then 48 else
  if L=11 then 62 else
  if L=13 then 80 else
  if L=15 then 98 else
  if L=17 then 116 else
  0

theorem upper_attains {k : ℕ} [NeZero k] (q l : ZMod k) (L : ℤ)
    (hL : L ∈ SMFiniteLeptonSupport.leptonRange 3)
    (hc : (3 : ZMod k)*q+(L : ZMod k)*l=0) : Attains q l L (upperGrade L) := by
  obtain ⟨hbound,hpar⟩ := (SMFiniteLeptonSupport.mem_range 3 L).mp hL
  have hb := SMFiniteLeptonSupport.b1_lepton_bound L hL
  obtain ⟨hlo,hhi⟩ := abs_le.mp hb
  interval_cases L <;> norm_num at hpar
  · exact n17_attains q l (by simpa using hc)
  · exact n15_attains q l (by simpa using hc)
  · exact n13_attains q l (by simpa using hc)
  · exact n11_attains q l (by simpa using hc)
  · exact n9_attains q l (by simpa using hc)
  · exact n7_attains q l (by simpa using hc)
  · exact n5_attains q l (by simpa using hc)
  · exact n3_attains q l (by simpa using hc)
  · exact n1_attains q l (by simpa using hc)
  · exact p1_attains q l (by simpa using hc)
  · exact p3_attains q l (by simpa using hc)
  · exact p5_attains q l (by simpa using hc)
  · exact p7_attains q l (by simpa using hc)
  · exact p9_attains q l (by simpa using hc)
  · exact p11_attains q l (by simpa using hc)
  · exact p13_attains q l (by simpa using hc)
  · exact p15_attains q l (by simpa using hc)
  · exact p17_attains q l (by simpa using hc)

end Physics.SMB1DimensionWitnesses
