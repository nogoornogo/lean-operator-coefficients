import Physics.StandardModel.Operators.SMB1MinimumClassification

/-! Consumers distinguish proved minima from retained nontrivial intervals. -/
namespace GUT.SMB1MinimumClassificationExamples
open Math SMB1MinimumClassification SMMinimumOperatorDimension

theorem k3_exact : IsMinimum (1 : ZMod 3) 1 3 18 :=
  row_exact ⟨3,1,1,false,false⟩ 18 (by decide +kernel) (by decide +kernel)

theorem k5_exact : IsMinimum (1 : ZMod 5) 1 3 20 :=
  row_exact ⟨5,1,1,false,false⟩ 20 (by decide +kernel) (by decide +kernel)

/-- This retained interval is not asserted to be an exact minimum. -/
theorem k5_gap : rowLower ⟨5,1,3,false,false⟩=some 12 ∧
    rowUpper ⟨5,1,3,false,false⟩=some 14 := by decide +kernel

theorem k11_gap : rowLower ⟨11,0,1,false,false⟩=some 42 ∧
    rowUpper ⟨11,0,1,false,false⟩=some 62 := by decide +kernel

theorem k11_actual_upper :
    ∃ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ), (SMQLPatternRequests.blCharge p).1.natAbs=3 ∧
      SelectionCriteria.Allowed
        (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (0 : ZMod 11) 1) p h d) ∧
      SMChargeDegreeBounds.twiceDimension n h d=62 :=
  upper_attainment 0 1 62 (by decide +kernel)

theorem all_row_consumer (i : Fin 11) (r : SMFiniteLeptonAssignments.Row) [NeZero r.k]
    (hr : r ∈ SMFiniteLeptonAssignments.batches i) (hc : exactCheck r=true) :
    ∃ M, rowLower r=some M ∧ IsMinimum (r.q : ZMod r.k) r.l 3 M :=
  exact_check_semantics i r hr hc

end GUT.SMB1MinimumClassificationExamples
