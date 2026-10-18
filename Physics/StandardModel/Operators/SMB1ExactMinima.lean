import Physics.StandardModel.Operators.SMB1StrongDimensionBounds
import Physics.StandardModel.Operators.SMB1MinimumClassification

/-! Complete original-space B1 minimum grades on the existing 572-row domain. -/
namespace GUT.SMB1ExactMinima
set_option autoImplicit false
open Math SMFiniteLeptonAssignments SMFiniteLeptonDegreeBounds SMFiniteLeptonSupport
open SMB1MinimumClassification SMB1DimensionWitnesses SMMinimumOperatorDimension

/-- None denotes all-degree prohibition; Some is certified below on this domain. -/
def lowerMinimum {k : ℕ} (q l : ZMod k) : Option ℕ :=
  minimum SMB1StrongDimensionBounds.lowerGrade q l

def rowMinimum (r : Row) : Option ℕ := lowerMinimum (r.q : ZMod r.k) r.l

theorem universal_lower {k : ℕ} [NeZero k] (q l : ZMod k) (M : ℕ)
    (hm : lowerMinimum q l=some M) {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)
    (h d : ℕ) (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    M ≤ SMChargeDegreeBounds.twiceDimension n h d := by
  obtain ⟨L,hL,hq,hd⟩ := SMB1StrongDimensionBounds.original_lower q l p h d hb ha
  have hv : SMB1StrongDimensionBounds.lowerGrade L ∈
      values SMB1StrongDimensionBounds.lowerGrade q l :=
    Finset.mem_image.mpr ⟨L,Finset.mem_filter.mpr ⟨hL,hq⟩,rfl⟩
  exact le_trans ((minimum_some_spec _ q l M hm).2 _ hv) hd

theorem exact_of_match {k : ℕ} [NeZero k] (q l : ZMod k) (M : ℕ)
    (hl : lowerMinimum q l=some M) (hu : minimum upperGrade q l=some M) :
    IsMinimum q l 3 M :=
  ⟨upper_attainment q l M hu,fun _ p h d hb ha => universal_lower q l M hl p h d hb ha⟩

/-- Complete finite arithmetic, separately bridged to actual coefficients. -/
theorem numeric_match : ∀ i : Fin 11,
    (batches i).all (fun r => rowMinimum r==rowUpper r)=true := by
  decide +kernel

theorem row_match (i : Fin 11) (r : Row) (hr : r ∈ batches i) :
    rowMinimum r=rowUpper r := by
  simpa only [beq_iff_eq] using (List.all_eq_true.mp (numeric_match i)) r hr

/-- Every one of the 326 allowed rows has an attained global minimum. -/
theorem row_minimum (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i)
    (ha : r.b1Forbidden=false) :
    ∃ M, rowMinimum r=some M ∧ rowUpper r=some M ∧
      IsMinimum (r.q : ZMod r.k) r.l 3 M := by
  obtain ⟨_,M,_,hu,_,_,_⟩ := row_certificate i r hr ha
  have hl := (row_match i r hr).trans hu
  exact ⟨M,hl,hu,exact_of_match _ _ M hl hu⟩

theorem none_iff_forbidden {k : ℕ} [NeZero k] (q l : ZMod k) :
    lowerMinimum q l=none ↔
      SMQLPatternRequests.OriginalForbidden q l (fun c => c.1.natAbs=3) :=
  minimum_none_iff SMB1StrongDimensionBounds.lowerGrade q l

theorem row_none_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    rowMinimum r=none ↔ r.b1Forbidden=true :=
  (none_iff_forbidden _ _).trans (b1_forbidden_iff i r hr)

/-- Smaller grades are forbidden for every content and Higgs degree. -/
theorem row_forbidden_below (r : Row) [NeZero r.k] (M : ℕ) (hm : rowMinimum r=some M)
    {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (hd : SMChargeDegreeBounds.twiceDimension n h d < M) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d) := by
  apply (SelectionCriteria.forbidden_iff_not_allowed _).mpr
  intro ha
  have := universal_lower _ _ M hm p h d hb ha
  omega

def minimumCount (M : Option ℕ) : ℕ := (rows.filter (fun r => rowMinimum r==M)).length

theorem minimum_distribution :
    minimumCount none=246 ∧ minimumCount (some 14)=48 ∧ minimumCount (some 18)=98 ∧
    minimumCount (some 20)=62 ∧ minimumCount (some 28)=28 ∧ minimumCount (some 30)=16 ∧
    minimumCount (some 38)=16 ∧ minimumCount (some 40)=10 ∧ minimumCount (some 48)=28 ∧
    minimumCount (some 54)=10 ∧ minimumCount (some 62)=10 := by
  decide +kernel

theorem classified_count :
    minimumCount (some 14)+minimumCount (some 18)+minimumCount (some 20)+
    minimumCount (some 28)+minimumCount (some 30)+minimumCount (some 38)+
    minimumCount (some 40)+minimumCount (some 48)+minimumCount (some 54)+
    minimumCount (some 62)=326 := by
  obtain ⟨_,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := minimum_distribution
  omega

end GUT.SMB1ExactMinima
