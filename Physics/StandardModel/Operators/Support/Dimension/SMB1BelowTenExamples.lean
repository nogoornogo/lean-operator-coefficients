import Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTenAssignments

/-! Importing controls of bounded support, row semantics and the strict cutoff. -/
namespace Physics.SMB1BelowTenExamples
open Math SMB1BelowTen

theorem dimension_six_control : Allowed (0 : ZMod 2) 0 :=
  plus_one_sufficient 0 0 (by decide +kernel)

theorem dimension_seven_control : Allowed (1 : ZMod 5) 3 :=
  minus_one_sufficient 1 3 (by decide +kernel)

theorem dimension_nine_control : Allowed (1 : ZMod 3) 1 :=
  plus_three_sufficient 1 1 (by decide +kernel)

theorem strict_boundary_forbidden : Forbidden (1 : ZMod 5) 1 :=
  (forbidden_iff 1 1).mpr (by decide +kernel)

theorem strict_boundary_minimum :
    SMMinimumOperatorDimension.IsMinimum (1 : ZMod 5) 1 3 20 :=
  SMMinimumOperatorDimension.h2_minimum

/-- The strict bounded prohibition is compatible with actual all-degree allowance. -/
theorem strict_boundary_later_allowed :
    Forbidden (1 : ZMod 5) 1 ∧
    SMQLPatternRequests.OriginalAllowed (1 : ZMod 5) 1 (fun c => c.1.natAbs=3) := by
  refine ⟨strict_boundary_forbidden,?_⟩
  obtain ⟨n,p,h,d,hb,ha,_⟩ := strict_boundary_minimum.attained
  exact ⟨n,p,h,d,hb,ha⟩

theorem negative_baryon_control {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)
    (h d : ℕ) (hb : (SMQLPatternRequests.blCharge p).1= -3)
    (hd : SMChargeDegreeBounds.twiceDimension n h d < 20) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (1 : ZMod 5) 1) p h d) := by
  apply strict_boundary_forbidden n p h d _ hd
  rw [hb]
  decide +kernel

theorem counted_row_consumer (i : Fin 11) (r : SMFiniteLeptonAssignments.Row)
    [NeZero r.k] (hr : r ∈ SMFiniteLeptonAssignments.batches i)
    (hc : SMB1BelowTenAssignments.check r=false) (ha : r.b1Forbidden=false) :
    Forbidden (r.q : ZMod r.k) r.l ∧
    SMQLPatternRequests.OriginalAllowed (r.q : ZMod r.k) r.l (fun c => c.1.natAbs=3) :=
  (SMB1BelowTenAssignments.later_allowed_semantics i r hr).mpr ⟨hc,ha⟩

end Physics.SMB1BelowTenExamples
