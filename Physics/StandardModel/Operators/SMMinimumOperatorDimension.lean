import Physics.StandardModel.Operators.SMFiniteLeptonDegreeBounds

/-! Exact engineering-dimension minima for four fixed scalar cyclic inputs.
All minima refer to actual original coefficient spaces, with all Higgs degrees. -/
namespace GUT.SMMinimumOperatorDimension
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds
open scoped BigOperators

attribute [local instance] SMCompactSupportDecision.expressionDecision
attribute [local instance] SMCompactSupportDecision.jointDecision

/-- A value is attained and bounds every selected original allowed content. -/
structure IsMinimum {k : ℕ} [NeZero k] (q l : ZMod k) (b M : ℕ) : Prop where
  attained : ∃ (n : ℕ) (p : Fin n → Species) (h d : ℕ),
    (SMQLPatternRequests.blCharge p).1.natAbs = b ∧
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ∧
    twiceDimension n h d = M
  lower : ∀ (n : ℕ) (p : Fin n → Species) (h d : ℕ),
    (SMQLPatternRequests.blCharge p).1.natAbs = b →
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) →
    M ≤ twiceDimension n h d

theorem IsMinimum.unique {k : ℕ} [NeZero k] {q l : ZMod k} {b M N : ℕ}
    (hm : IsMinimum q l b M) (hn : IsMinimum q l b N) : M=N := by
  obtain ⟨n,p,h,d,hb,ha,he⟩ := hm.attained
  obtain ⟨n',p',h',d',hb',ha',he'⟩ := hn.attained
  have hmn := hm.lower n' p' h' d' hb' ha'
  have hnm := hn.lower n p h d hb ha
  omega

/-- A certificate excludes every smaller grading in the same actual domain. -/
theorem IsMinimum.forbidden_below {k : ℕ} [NeZero k] {q l : ZMod k} {b M : ℕ}
    (hm : IsMinimum q l b M) {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=b)
    (hd : twiceDimension n h d < M) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) := by
  apply (SelectionCriteria.forbidden_iff_not_allowed _).mpr
  intro ha
  have := hm.lower n p h d hb ha
  omega

def c1Pattern : Fin 4 → Species := ![0,0,0,3]
def c1Counts : Species → ℕ := ![3,0,0,1,0,0,0,0,0,0]

theorem c1_counts : SMIteratedContent.counts c1Pattern = c1Counts := by
  funext t
  fin_cases t <;> decide +kernel

theorem c1_support : SMJointContentSupport.Supports c1Counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced c1Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem c1_allowed : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (0 : ZMod 2) 0) c1Pattern 0 0) := by
  apply (SMJointHiggsSupport.original_ql_iff c1Pattern 0 0 0 0).mpr
  refine ⟨by decide +kernel, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [c1_counts]
    exact c1_support

theorem c1_charge_minimum :
    SMFiniteLeptonDegreeBounds.minLepton 3 (0 : ZMod 2) 0 = some 1 := by
  decide +kernel

theorem c1_minimum : IsMinimum (0 : ZMod 2) 0 3 12 := by
  constructor
  · exact ⟨4,c1Pattern,0,0,by decide +kernel,c1_allowed,rfl⟩
  · intro n p h d hb ha
    exact (SMFiniteLeptonDegreeBounds.original_degree_lower 3 0 0 1
      c1_charge_minimum p h d hb ha).2

def c2Pattern : Fin 6 → Species := ![1,1,2,2,2,2]
def c2Counts : Species → ℕ := ![0,2,4,0,0,0,0,0,0,0]

theorem c2_counts : SMIteratedContent.counts c2Pattern = c2Counts := by
  funext t
  fin_cases t <;> decide +kernel

theorem c2_support : SMJointContentSupport.Supports c2Counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced c2Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem c2_allowed : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (0 : ZMod 2) 0) c2Pattern 0 0) := by
  apply (SMJointHiggsSupport.original_ql_iff c2Pattern 0 0 0 0).mpr
  refine ⟨by decide +kernel, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [c2_counts]
    exact c2_support

theorem c2_charge_minimum :
    SMFiniteLeptonDegreeBounds.minLepton 6 (0 : ZMod 2) 0 = some 0 := by
  decide +kernel

theorem c2_minimum : IsMinimum (0 : ZMod 2) 0 6 18 := by
  constructor
  · exact ⟨6,c2Pattern,0,0,by decide +kernel,c2_allowed,rfl⟩
  · intro n p h d hb ha
    exact (SMFiniteLeptonDegreeBounds.original_degree_lower 6 0 0 0
      c2_charge_minimum p h d hb ha).2

def h1Pattern : Fin 6 → Species := ![1,1,1,3,3,4]
def h1Counts : Species → ℕ := ![0,3,0,2,1,0,0,0,0,0]

theorem h1_counts : SMIteratedContent.counts h1Pattern = h1Counts := by
  funext t
  fin_cases t <;> decide +kernel

theorem h1_support : SMJointContentSupport.Supports h1Counts 0 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced h1Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem h1_allowed : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (1 : ZMod 3) 1) h1Pattern 0 0) := by
  apply (SMJointHiggsSupport.original_ql_iff h1Pattern 1 1 0 0).mpr
  refine ⟨by decide +kernel, by decide +kernel, ⟨⟨0, by decide +kernel⟩, ?_, ?_⟩⟩
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [h1_counts]
    exact h1_support

theorem h1_charge_minimum :
    SMFiniteLeptonDegreeBounds.minLepton 3 (1 : ZMod 3) 1 = some 3 := by
  decide +kernel

theorem h1_minimum : IsMinimum (1 : ZMod 3) 1 3 18 := by
  constructor
  · exact ⟨6,h1Pattern,0,0,by decide +kernel,h1_allowed,rfl⟩
  · intro n p h d hb ha
    exact (SMFiniteLeptonDegreeBounds.original_degree_lower 3 1 1 3
      h1_charge_minimum p h d hb ha).2

def h2Pattern : Fin 6 → Species := ![2,2,2,8,8,8]
def h2Counts : Species → ℕ := ![0,0,3,0,0,0,0,0,3,0]

theorem h2_counts : SMIteratedContent.counts h2Pattern = h2Counts := by
  funext t
  fin_cases t <;> decide +kernel

theorem h2_support : SMJointContentSupport.Supports h2Counts 1 := by
  apply (SMJointContentSupport.supports_iff_choices _ _).mpr
  refine ⟨SMLeptonChargeWitnesses.balanced h2Counts,
    SMLeptonChargeWitnesses.firstBranch _ (by decide +kernel), ?_⟩
  decide +kernel

theorem h2_allowed : SelectionCriteria.Allowed
    (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (1 : ZMod 5) 1) h2Pattern 0 1) := by
  apply (SMJointHiggsSupport.original_ql_iff h2Pattern 1 1 0 1).mpr
  refine ⟨by decide +kernel, by decide +kernel, ⟨⟨1, by decide +kernel⟩, ?_, ?_⟩⟩
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [h2_counts]
    exact h2_support

theorem h2_charge_minimum :
    SMFiniteLeptonDegreeBounds.minLepton 3 (1 : ZMod 5) 1 = some 3 := by
  decide +kernel

/-- A finite dictionary inequality, independent of coefficient allowance. -/
theorem species_hypercharge_envelope (s : Species) :
    |hypercharge s - baryon s + 6*lepton s| ≤ 3 := by
  fin_cases s <;> decide +kernel

/-- A joint charge bound retaining actual hypercharge. -/
theorem hypercharge_envelope {n : ℕ} (p : Fin n → Species) :
    |SMContentWeakBound.hypercharge p - (SMQLPatternRequests.blCharge p).1 +
      6*(SMQLPatternRequests.blCharge p).2| ≤ 3*(n : ℤ) := by
  change |(∑ i, hypercharge (p i)) - (∑ i, baryon (p i)) +
    6*(∑ i, lepton (p i))| ≤ _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ i, |hypercharge (p i) - baryon (p i) + 6*lepton (p i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (3 : ℤ) :=
      Finset.sum_le_sum (fun i _ => species_hypercharge_envelope (p i))
    _ = _ := by simp; ring

/-- No content of either baryon sign survives below doubled dimension 20. -/
theorem h2_lower {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (1 : ZMod 5) 1) p h d)) :
    20 ≤ twiceDimension n h d := by
  have hn := (SMFiniteLeptonDegreeBounds.original_degree_lower 3 1 1 3
    h2_charge_minimum p h d hb ha).1
  have heven := original_even (1 : ZMod 5) 1 p h d ha
  have hparity := original_parity (1 : ZMod 5) 1 p h d ha
  have hcharge := charge_degree p
  have habs : |(SMQLPatternRequests.blCharge p).1| = 3 := by
    rw [← Int.natCast_natAbs, hb]
    rfl
  rw [habs] at hcharge
  have hl : |(SMQLPatternRequests.blCharge p).2| ≤ (n : ℤ)-3 := by omega
  rw [abs_le] at hl
  have henv := hypercharge_envelope p
  obtain ⟨hc,hy,_⟩ := (SMJointHiggsSupport.original_ql_iff p (1 : ZMod 5) 1 h d).mp ha
  have hc' : (((SMQLPatternRequests.blCharge p).1 +
      (SMQLPatternRequests.blCharge p).2 : ℤ) : ZMod 5)=0 := by
    rw [residual_linear] at hc
    simpa only [Int.cast_add, mul_one] using hc
  have hm : ((SMQLPatternRequests.blCharge p).1 +
      (SMQLPatternRequests.blCharge p).2) % 5 = 0 :=
    Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hc')
  rw [abs_le] at henv
  rcases Int.natAbs_eq_iff.mp hb with hb | hb <;>
    unfold twiceDimension <;> omega

theorem h2_minimum : IsMinimum (1 : ZMod 5) 1 3 20 := by
  constructor
  · exact ⟨6,h2Pattern,0,1,by decide +kernel,h2_allowed,rfl⟩
  · intro n p h d hb ha
    exact h2_lower p h d hb ha

end GUT.SMMinimumOperatorDimension
