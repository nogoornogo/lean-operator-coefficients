import Physics.StandardModel.Operators.Support.Dimension.SMB1WeakCountArithmetic

/-! Small dictionary and support bridges to the abstract count arithmetic. -/
namespace Physics.SMB1WeakDimensionBounds
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds SMFiniteLeptonSupport
open scoped BigOperators

/-- Each sum is proved once, without carrying a coefficient-space hypothesis. -/
theorem counts_total {n : ℕ} (p : Fin n → Species) :
    SMB1WeakCountArithmetic.total (SMIteratedContent.counts p)=n := by
  have he := sum_by_species p (fun _ => (1 : ℤ))
  simp [Fin.sum_univ_succ] at he
  unfold SMB1WeakCountArithmetic.total
  omega

theorem counts_baryon {n : ℕ} (p : Fin n → Species) :
    (SMQLPatternRequests.blCharge p).1=SMB1WeakCountArithmetic.baryon (SMIteratedContent.counts p) := by
  change (∑ i, baryon (p i)) = _
  rw [sum_by_species]
  simp [baryon,SMB1WeakCountArithmetic.baryon,Fin.sum_univ_succ]
  ring

theorem counts_lepton {n : ℕ} (p : Fin n → Species) :
    (SMQLPatternRequests.blCharge p).2=SMB1WeakCountArithmetic.lepton (SMIteratedContent.counts p) := by
  change (∑ i, lepton (p i)) = _
  rw [sum_by_species]
  simp [lepton,SMB1WeakCountArithmetic.lepton,Fin.sum_univ_succ]
  ring

theorem counts_hypercharge {n : ℕ} (p : Fin n → Species) :
    SMContentWeakBound.hypercharge p=SMB1WeakCountArithmetic.hypercharge (SMIteratedContent.counts p) := by
  change (∑ i, hypercharge (p i)) = _
  rw [sum_by_species]
  simp [hypercharge,SMB1WeakCountArithmetic.hypercharge,Fin.sum_univ_succ]
  ring

theorem original_delta_bounds {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    -((SMMixedWeakCapacity.bound p : ℕ) : ℤ) ≤ (h : ℤ)-d ∧
      (h : ℤ)-d ≤ (SMMixedWeakCapacity.bound p : ℕ) := by
  by_contra hn
  have hx : (SMMixedWeakCapacity.bound p : ℤ) < (h : ℤ)-d ∨
      (h : ℤ)-d < -(SMMixedWeakCapacity.bound p : ℤ) := by omega
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMMixedWeakCapacity.original_ql_forbidden p q l h d hx) ha

theorem original_count_bounds {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    (h : ℤ)-d ≤ (SMIteratedContent.counts p 0 : ℤ)+SMIteratedContent.counts p 5+
      12-SMIteratedContent.counts p 3+SMIteratedContent.counts p 8 ∧
    (d : ℤ)-h ≤ (SMIteratedContent.counts p 0 : ℤ)+SMIteratedContent.counts p 5+
      12+SMIteratedContent.counts p 3-SMIteratedContent.counts p 8 := by
  have hfit := SMFiniteLeptonSupport.original_fits q l p h d ha
  have hc3 := hfit 3
  have hc8 := hfit 8
  rw [SMConstantWeakCapacity.dimension_eq] at hc3 hc8
  norm_num at hc3 hc8
  have hb := SMB1WeakCountArithmetic.capacity_sums (SMIteratedContent.counts p) hc3 hc8
  change SMMixedWeakCapacity.bound p ≤ _ ∧ SMMixedWeakCapacity.bound p ≤ _ at hb
  have hw := original_delta_bounds q l p h d ha
  constructor <;> omega

/-- Actual support enters only through three already extracted scalar conditions. -/
theorem original_weak_envelope {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    |7*(SMQLPatternRequests.blCharge p).2-(SMQLPatternRequests.blCharge p).1| ≤
      12+(twiceDimension n h d : ℤ) := by
  obtain ⟨hp,hn⟩ := original_count_bounds q l p h d ha
  have hy := ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).2.1
  rw [counts_hypercharge] at hy
  have he := SMB1WeakCountArithmetic.weak_envelope (SMIteratedContent.counts p) h d hy hp hn
  rw [← counts_baryon,← counts_lepton,counts_total] at he
  simpa only [twiceDimension,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,add_assoc] using he

end Physics.SMB1WeakDimensionBounds
