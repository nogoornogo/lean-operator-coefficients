import Physics.StandardModel.Operators.Support.Dimension.SMFiniteLeptonDegreeBounds

/-! Importing consumers of default-build minima and original-space bounds. -/
namespace Physics.SMFiniteLeptonDegreeExamples
open Math SMChargeDegreeBounds SMFiniteLeptonDegreeBounds

theorem k101_none : minLepton 3 (10 : ZMod 101) 1=none := by decide +kernel
theorem k101_minimum : minLepton 3 (28 : ZMod 101) 1=some 17 := by decide +kernel

theorem k3_b1_bounds {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (0 : ZMod 3) 1) p h d)) :
    6 ≤ n ∧ 18 ≤ twiceDimension n h d :=
  high_row_bounds 3 3 ⟨3,0,1,false,false⟩ (by decide +kernel) p h d hb ha

theorem k4_b2_bounds {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=6)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (1 : ZMod 4) 3) p h d)) :
    8 ≤ n ∧ 24 ≤ twiceDimension n h d :=
  high_row_bounds 6 2 ⟨4,1,3,false,false⟩ (by decide +kernel) p h d hb ha

theorem negative_baryon_bound {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1 = -3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (28 : ZMod 101) 1) p h d)) :
    20 ≤ n ∧ 60 ≤ twiceDimension n h d := by
  apply original_degree_lower 3 (28 : ZMod 101) 1 17 k101_minimum p h d _ ha
  rw [hb]
  decide +kernel

end Physics.SMFiniteLeptonDegreeExamples
