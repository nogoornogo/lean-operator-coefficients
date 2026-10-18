import Physics.StandardModel.Operators.SMMinimumOperatorDimension

/-! Fresh importing consumers of the four exact original-space minima. -/
namespace GUT.SMMinimumOperatorDimensionExamples
open Math SMChargeDegreeBounds SMMinimumOperatorDimension

theorem exact_minima :
    IsMinimum (0 : ZMod 2) 0 3 12 ∧ IsMinimum (0 : ZMod 2) 0 6 18 ∧
    IsMinimum (1 : ZMod 3) 1 3 18 ∧ IsMinimum (1 : ZMod 5) 1 3 20 :=
  ⟨c1_minimum,c2_minimum,h1_minimum,h2_minimum⟩

/-- The old charge lower bound is strictly below the true H2 minimum. -/
theorem charge_bound_not_attained : ¬ IsMinimum (1 : ZMod 5) 1 3 18 := by
  intro hm
  have := hm.unique h2_minimum
  omega

/-- Reject an incorrect larger minimum despite its valid lower-bound claim. -/
theorem no_larger_minimum : ¬ IsMinimum (1 : ZMod 5) 1 3 22 := by
  intro hm
  have := hm.unique h2_minimum
  omega

theorem h2_no_six_fermions_without_higgs (p : Fin 6 → DeltaLOneSignedInput.Species)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (1 : ZMod 5) 1) p 0 0) :=
  h2_minimum.forbidden_below p 0 0 hb (by decide +kernel)

theorem h2_negative_baryon {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1 = -3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (1 : ZMod 5) 1) p h d)) :
    20 ≤ twiceDimension n h d := by
  apply h2_minimum.lower n p h d _ ha
  rw [hb]
  decide +kernel

theorem h2_witness_charge : SMQLPatternRequests.blCharge h2Pattern = (3,-3) := by
  decide +kernel

end GUT.SMMinimumOperatorDimensionExamples
