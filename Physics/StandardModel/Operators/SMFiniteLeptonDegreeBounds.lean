import Physics.StandardModel.Operators.SMFiniteLeptonAssignments

/-! The minimum attainable absolute lepton charge and uniform degree bounds.
None denotes prohibition. This is not minimum engineering dimension. -/
namespace GUT.SMFiniteLeptonDegreeBounds
set_option autoImplicit false
open Math SMFiniteLeptonSupport SMChargeDegreeBounds

def neutralLeptons (b : ℕ) {k : ℕ} (q l : ZMod k) : Finset ℤ :=
  (leptonRange b).filter (fun L => (b : ZMod k)*q + (L : ZMod k)*l=0)

def leptonSizes (b : ℕ) {k : ℕ} (q l : ZMod k) : Finset ℕ :=
  (neutralLeptons b q l).image Int.natAbs

def minLepton (b : ℕ) {k : ℕ} (q l : ZMod k) : Option ℕ :=
  if h : (leptonSizes b q l).Nonempty then some ((leptonSizes b q l).min' h) else none

theorem sizes_nonempty_iff (b : ℕ) {k : ℕ} (q l : ZMod k) :
    (leptonSizes b q l).Nonempty ↔
      ∃ L ∈ leptonRange b, (b : ZMod k)*q + (L : ZMod k)*l=0 := by
  simp only [leptonSizes, Finset.image_nonempty, neutralLeptons, Finset.filter_nonempty_iff]

theorem min_none_iff (b : ℕ) {k : ℕ} (q l : ZMod k) :
    minLepton b q l=none ↔ ¬(leptonSizes b q l).Nonempty := by
  by_cases h : (leptonSizes b q l).Nonempty <;> simp [minLepton,h]

theorem min_some_spec (b : ℕ) {k : ℕ} (q l : ZMod k) (m : ℕ)
    (hm : minLepton b q l=some m) :
    m ∈ leptonSizes b q l ∧ ∀ v ∈ leptonSizes b q l, m ≤ v := by
  have hn : (leptonSizes b q l).Nonempty := by
    by_contra hn
    simp [minLepton,hn] at hm
  have he : (leptonSizes b q l).min' hn=m := by simpa [minLepton,hn] using hm
  rw [← he]
  exact ⟨Finset.min'_mem _ _,fun v hv => Finset.min'_le _ v hv⟩

theorem min_none_forbidden (b : ℕ) (hb : b=3 ∨ b=6) {k : ℕ} [NeZero k] (q l : ZMod k) :
    minLepton b q l=none ↔
      SMQLPatternRequests.OriginalForbidden q l (fun c => c.1.natAbs=b) := by
  rw [min_none_iff, sizes_nonempty_iff,
    ← SMQLPatternRequests.forbidden_iff_original,
    SelectionCriteria.forbidden_iff_not_allowed, SMQLPatternRequests.allowed_iff_original,
    SMFiniteLeptonSupport.original_allowed_iff q l b hb]

/-- The minimum charge is realized in an actual coefficient space. -/
theorem minimum_attained (b : ℕ) (hb : b=3 ∨ b=6) {k : ℕ} [NeZero k] (q l : ZMod k)
    (m : ℕ) (hm : minLepton b q l=some m) :
    ∃ L : ℤ, L.natAbs=m ∧
      SMQLPatternRequests.OriginalAllowed q l (fun c => c=((b : ℤ),L)) := by
  obtain ⟨L,hL,he⟩ := Finset.mem_image.mp (min_some_spec b q l m hm).1
  have hs := Finset.mem_filter.mp hL
  exact ⟨L,he,(exact_original_iff q l b hb L).mpr hs⟩

/-- Preserve the actual |L| while normalizing the sign of baryon charge. -/
theorem normalized_content (b : ℕ) {k : ℕ} [NeZero k] (q l : ZMod k)
    {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=b)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    ∃ L ∈ neutralLeptons b q l, L.natAbs=(SMQLPatternRequests.blCharge p).2.natAbs := by
  have hl := original_lepton_capacity q l p h d ha
  have hp := original_parity q l p h d ha
  have hc := (residual_linear q l p).symm.trans
    ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).1
  rcases Int.natAbs_eq_iff.mp hb with hb | hb
  · refine ⟨(SMQLPatternRequests.blCharge p).2, Finset.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · apply (mem_range b _).mpr
      exact ⟨hl,by simpa only [hb] using hp⟩
    · simpa only [hb,Int.cast_natCast] using hc
  · refine ⟨-(SMQLPatternRequests.blCharge p).2, Finset.mem_filter.mpr ⟨?_,?_⟩,by simp⟩
    · apply (mem_range b _).mpr
      exact ⟨by simpa only [abs_neg] using hl,by omega⟩
    · rw [hb] at hc
      push_cast at hc ⊢
      linear_combination -hc

/-- Every allowed content, including negative B3, obeys this charge bound. -/
theorem original_lepton_lower (b : ℕ) {k : ℕ} [NeZero k] (q l : ZMod k)
    (m : ℕ) (hm : minLepton b q l=some m)
    {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=b)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    m ≤ (SMQLPatternRequests.blCharge p).2.natAbs := by
  obtain ⟨L,hL,he⟩ := normalized_content b q l p h d hb ha
  rw [← he]
  exact (min_some_spec b q l m hm).2 _ (Finset.mem_image.mpr ⟨L,hL,rfl⟩)

theorem original_degree_lower (b : ℕ) {k : ℕ} [NeZero k] (q l : ZMod k)
    (m : ℕ) (hm : minLepton b q l=some m)
    {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=b)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    b+m ≤ n ∧ 3*(b+m) ≤ twiceDimension n h d := by
  have hl := original_lepton_lower b q l m hm p h d hb ha
  have hn := selected_degree p b hb
  have he := Int.natCast_natAbs (SMQLPatternRequests.blCharge p).2
  unfold twiceDimension
  constructor <;> omega

theorem min_exists_iff (b : ℕ) (hb : b=3 ∨ b=6) {k : ℕ} [NeZero k] (q l : ZMod k) :
    (∃ m, minLepton b q l=some m) ↔
      SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=b) := by
  rw [SMFiniteLeptonAssignments.allowed_not_forbidden, ← min_none_forbidden b hb q l]
  cases minLepton b q l <;> simp

theorem minimum_le_eighteen (b : ℕ) {k : ℕ} (q l : ZMod k) (m : ℕ)
    (hm : minLepton b q l=some m) : m ≤ 18 := by
  obtain ⟨L,hL,he⟩ := Finset.mem_image.mp (min_some_spec b q l m hm).1
  have hl := ((mem_range b L).mp (Finset.mem_filter.mp hL).1).1
  have hn := Int.natCast_natAbs L
  omega

open SMFiniteLeptonAssignments

def rowMinimum (b : ℕ) (r : Row) : Option ℕ := minLepton b (r.q : ZMod r.k) r.l

theorem b1_minimum_none_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    rowMinimum 3 r=none ↔ r.b1Forbidden=true :=
  (min_none_forbidden 3 (Or.inl rfl) _ _).trans (SMFiniteLeptonAssignments.b1_forbidden_iff i r hr)

theorem b2_minimum_none_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    rowMinimum 6 r=none ↔ r.b2Forbidden=true :=
  (min_none_forbidden 6 (Or.inr rfl) _ _).trans (SMFiniteLeptonAssignments.b2_forbidden_iff i r hr)

theorem b1_minimum_some_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    (∃ m, rowMinimum 3 r=some m) ↔ r.b1Forbidden=false :=
  (min_exists_iff 3 (Or.inl rfl) _ _).trans (SMFiniteLeptonAssignments.b1_allowed_iff i r hr)

theorem b2_minimum_some_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    (∃ m, rowMinimum 6 r=some m) ↔ r.b2Forbidden=false :=
  (min_exists_iff 6 (Or.inr rfl) _ _).trans (SMFiniteLeptonAssignments.b2_allowed_iff i r hr)

/-- Each allowed B1 row has a single computed minimum bounding all its contents. -/
theorem b1_row_bounds (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i)
    (hf : r.b1Forbidden=false) :
    ∃ m, rowMinimum 3 r=some m ∧
      ∀ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ),
        (SMQLPatternRequests.blCharge p).1.natAbs=3 →
        SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
          (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d) →
        3+m ≤ n ∧ 3*(3+m) ≤ twiceDimension n h d := by
  obtain ⟨m,hm⟩ := (b1_minimum_some_iff i r hr).mpr hf
  exact ⟨m,hm,fun n p h d hb ha => original_degree_lower 3 _ _ m hm p h d hb ha⟩

/-- Each allowed B2 row has a single computed minimum bounding all its contents. -/
theorem b2_row_bounds (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i)
    (hf : r.b2Forbidden=false) :
    ∃ m, rowMinimum 6 r=some m ∧
      ∀ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ),
        (SMQLPatternRequests.blCharge p).1.natAbs=6 →
        SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
          (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d) →
        6+m ≤ n ∧ 3*(6+m) ≤ twiceDimension n h d := by
  obtain ⟨m,hm⟩ := (b2_minimum_some_iff i r hr).mpr hf
  exact ⟨m,hm,fun n p h d hb ha => original_degree_lower 6 _ _ m hm p h d hb ha⟩

def minimumCount (b : ℕ) (m : Option ℕ) : ℕ :=
  ∑ i, ((batches i).filter (fun r => rowMinimum b r==m)).length

/-- Every possible numeric minimum is covered; values above 18 are impossible. -/
theorem minimum_distributions :
    (List.range 19).map (fun m => minimumCount 3 (some m)) =
      [0,48,0,160,0,44,0,26,0,38,0,10,0,0,0,0,0,0,0] ∧
    (List.range 19).map (fun m => minimumCount 6 (some m)) =
      [186,0,72,0,80,0,92,0,20,0,20,0,0,0,0,0,0,0,0] ∧
    minimumCount 3 none=246 ∧ minimumCount 6 none=102 := by
  decide +kernel

def highLepton (b lower : ℕ) (r : Row) : Bool :=
  match rowMinimum b r with
  | none => false
  | some m => lower ≤ m

def highLeptonCount (b lower : ℕ) : ℕ :=
  ∑ i, ((batches i).filter (highLepton b lower)).length

theorem high_degree_counts : highLeptonCount 3 3=278 ∧ highLeptonCount 6 2=284 := by
  decide +kernel

/-- An assignment and a B target form one application: 326+470=796. -/
theorem allowed_application_count :
    (572-minimumCount 3 none)+(572-minimumCount 6 none)=796 := by
  obtain ⟨_,_,h1,h2⟩ := minimum_distributions
  omega

theorem high_row_bounds (b lower : ℕ) (r : Row) [NeZero r.k]
    (hh : highLepton b lower r=true)
    {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=b)
    (ha : SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d)) :
    b+lower ≤ n ∧ 3*(b+lower) ≤ twiceDimension n h d := by
  unfold highLepton at hh
  split at hh
  · contradiction
  · rename_i m hm
    have hl : lower ≤ m := by simpa using hh
    have hn := original_degree_lower b _ _ m hm p h d hb ha
    constructor <;> omega

end GUT.SMFiniteLeptonDegreeBounds
