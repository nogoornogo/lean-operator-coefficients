import Physics.StandardModel.Operators.Support.Dimension.SMB1ExactMinima

/-! Importing consumers of previously unresolved global B1 minima. -/
-- Elaborate the finite certificates sequentially within this module.
set_option Elab.async false

namespace Physics.SMB1ExactMinimaExamples
open Math SMB1ExactMinima SMMinimumOperatorDimension

theorem generic_weak_bound {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    |7*(SMQLPatternRequests.blCharge p).2-(SMQLPatternRequests.blCharge p).1| ≤
      12+(SMChargeDegreeBounds.twiceDimension n h d : ℤ) :=
  SMB1WeakDimensionBounds.original_weak_envelope q l p h d ha

/-- The old retained [6,7] interval is now closed at dimension seven. -/
theorem k5_minimum_seven : IsMinimum (1 : ZMod 5) 3 3 14 :=
  exact_of_match 1 3 14 (by decide +kernel) (by decide +kernel)

/-- The old retained [21,31] interval is now closed at dimension thirty-one. -/
theorem k11_minimum_thirty_one : IsMinimum (0 : ZMod 11) 1 3 62 :=
  exact_of_match 0 1 62 (by decide +kernel) (by decide +kernel)

theorem k2_none : lowerMinimum (0 : ZMod 2) 1=none := by decide +kernel

theorem k2_all_degree_forbidden :
    SMQLPatternRequests.OriginalForbidden (0 : ZMod 2) 1 (fun c => c.1.natAbs=3) :=
  (none_iff_forbidden 0 1).mp k2_none

theorem negative_baryon_below_minimum {n : ℕ}
    (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1= -3)
    (hd : SMChargeDegreeBounds.twiceDimension n h d<62) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (0 : ZMod 11) 1) p h d) := by
  apply k11_minimum_thirty_one.forbidden_below p h d _ hd
  rw [hb]
  decide +kernel

theorem generic_row_minimum (i : Fin 11) (r : SMFiniteLeptonAssignments.Row) [NeZero r.k]
    (hr : r ∈ SMFiniteLeptonAssignments.batches i) (ha : r.b1Forbidden=false) :
    ∃ M, rowMinimum r=some M ∧ SMB1MinimumClassification.rowUpper r=some M ∧
      IsMinimum (r.q : ZMod r.k) r.l 3 M := row_minimum i r hr ha

end Physics.SMB1ExactMinimaExamples
