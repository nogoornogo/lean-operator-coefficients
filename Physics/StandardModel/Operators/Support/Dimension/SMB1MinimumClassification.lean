import Physics.StandardModel.Operators.Support.Dimension.SMB1DimensionWitnesses

/-! Verified B1 grade intervals after a bounded complete-exclusion resource stop. -/
-- Elaborate the finite certificates sequentially within this module.
set_option Elab.async false

namespace Physics.SMB1MinimumClassification
set_option autoImplicit false
open Math SMFiniteLeptonAssignments SMFiniteLeptonDegreeBounds SMFiniteLeptonSupport
open SMB1DimensionBounds SMB1DimensionWitnesses SMMinimumOperatorDimension

def values (f : ℤ → ℕ) {k : ℕ} (q l : ZMod k) : Finset ℕ :=
  (neutralLeptons 3 q l).image f

def minimum (f : ℤ → ℕ) {k : ℕ} (q l : ZMod k) : Option ℕ :=
  if h : (values f q l).Nonempty then some ((values f q l).min' h) else none

theorem minimum_some_spec (f : ℤ → ℕ) {k : ℕ} (q l : ZMod k) (M : ℕ)
    (hm : minimum f q l=some M) :
    M ∈ values f q l ∧ ∀ v ∈ values f q l, M≤v := by
  have hn : (values f q l).Nonempty := by
    by_contra hn
    simp [minimum,hn] at hm
  have he : (values f q l).min' hn=M := by simpa [minimum,hn] using hm
  rw [← he]
  exact ⟨Finset.min'_mem _ _,fun v hv => Finset.min'_le _ v hv⟩

theorem minimum_none_iff (f : ℤ → ℕ) {k : ℕ} [NeZero k] (q l : ZMod k) :
    minimum f q l=none ↔
    SMQLPatternRequests.OriginalForbidden q l (fun c => c.1.natAbs=3) := by
  have he : minimum f q l=none ↔ ¬ (values f q l).Nonempty := by
    by_cases h : (values f q l).Nonempty <;> simp [minimum,h]
  rw [he]
  simp only [values,Finset.image_nonempty]
  simpa only [leptonSizes,Finset.image_nonempty] using
    ((SMFiniteLeptonDegreeBounds.min_none_iff 3 q l).symm.trans
      (min_none_forbidden 3 (Or.inl rfl) q l))

theorem universal_lower {k : ℕ} [NeZero k] (q l : ZMod k) (M : ℕ)
    (hm : minimum lowerGrade q l=some M) {n : ℕ}
    (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    M ≤ SMChargeDegreeBounds.twiceDimension n h d := by
  obtain ⟨L,hL,hq,hd⟩ := original_lower q l p h d hb ha
  have hv : lowerGrade L ∈ values lowerGrade q l := by
    apply Finset.mem_image.mpr
    exact ⟨L,Finset.mem_filter.mpr ⟨hL,hq⟩,rfl⟩
  exact le_trans ((minimum_some_spec lowerGrade q l M hm).2 _ hv) hd

theorem upper_attainment {k : ℕ} [NeZero k] (q l : ZMod k) (M : ℕ)
    (hm : minimum upperGrade q l=some M) :
    ∃ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ),
      (SMQLPatternRequests.blCharge p).1.natAbs=3 ∧
      SelectionCriteria.Allowed
        (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ∧
      SMChargeDegreeBounds.twiceDimension n h d=M := by
  obtain ⟨L,hL,he⟩ := Finset.mem_image.mp (minimum_some_spec upperGrade q l M hm).1
  obtain ⟨hL,hq⟩ := Finset.mem_filter.mp hL
  obtain ⟨n,p,h,d,hc,ha,hd⟩ := upper_attains q l L hL hq
  refine ⟨n,p,h,d,?_,ha,hd.trans he⟩
  rw [hc]
  change (3 : ℤ).natAbs=3
  decide +kernel

theorem exact_of_match {k : ℕ} [NeZero k] (q l : ZMod k) (M : ℕ)
    (hl : minimum lowerGrade q l=some M) (hu : minimum upperGrade q l=some M) :
    IsMinimum q l 3 M :=
  ⟨upper_attainment q l M hu,fun _ p h d hb ha => universal_lower q l M hl p h d hb ha⟩

def cutoffLower (r : Row) : ℕ := if SMB1BelowTenAssignments.check r then 0 else 20

def rowLower (r : Row) : Option ℕ :=
  (minimum lowerGrade (r.q : ZMod r.k) r.l).map (fun M => max M (cutoffLower r))
def rowUpper (r : Row) : Option ℕ := minimum upperGrade (r.q : ZMod r.k) r.l

theorem cutoff_lower (r : Row) [NeZero r.k] {n : ℕ}
    (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d)) :
    cutoffLower r ≤ SMChargeDegreeBounds.twiceDimension n h d := by
  unfold cutoffLower
  split_ifs with hc
  · omega
  · have hf := (SMB1BelowTenAssignments.row_forbidden_iff r).mpr (by cases he : SMB1BelowTenAssignments.check r <;> simp_all)
    by_contra hd
    exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
      (hf n p h d hb (by omega)) ha

theorem row_lower_bound (r : Row) [NeZero r.k] (M : ℕ) (hm : rowLower r=some M)
    {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d)) :
    M ≤ SMChargeDegreeBounds.twiceDimension n h d := by
  unfold rowLower at hm
  cases he : minimum lowerGrade (r.q : ZMod r.k) r.l with
  | none => simp [he] at hm
  | some N =>
    have heq : max N (cutoffLower r)=M := by simpa [he] using hm
    rw [← heq]
    exact max_le (universal_lower _ _ N he p h d hb ha) (cutoff_lower r p h d hb ha)

theorem row_exact (r : Row) [NeZero r.k] (M : ℕ)
    (hl : rowLower r=some M) (hu : rowUpper r=some M) :
    IsMinimum (r.q : ZMod r.k) r.l 3 M :=
  ⟨upper_attainment _ _ M hu,fun _ p h d hb ha => row_lower_bound r M hl p h d hb ha⟩

def intervalCheck (r : Row) : Bool :=
  decide ((rowLower r=none ↔ r.b1Forbidden=true) ∧
    (rowUpper r=none ↔ r.b1Forbidden=true)) &&
  match rowLower r,rowUpper r with
  | some L,some U => decide (L≤U)
  | _,_ => true

/-- Finite interval arithmetic, without asserting that every gap closes. -/
theorem numeric_inventory : ∀ i : Fin 11, (batches i).all intervalCheck=true := by
  decide +kernel

theorem row_intervals (i : Fin 11) (r : Row) (hr : r ∈ batches i) :
    (rowLower r=none ↔ r.b1Forbidden=true) ∧
    (rowUpper r=none ↔ r.b1Forbidden=true) ∧
    (∀ L ∈ rowLower r, ∀ U ∈ rowUpper r, L≤U) := by
  have hh := (List.all_eq_true.mp (numeric_inventory i)) r hr
  cases hl : rowLower r <;> cases hu : rowUpper r <;>
    simp [intervalCheck,hl,hu] at hh ⊢ <;> tauto

/-- Every allowed row has actual attainment at U and a universal lower bound L. -/
theorem row_certificate (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i)
    (ha : r.b1Forbidden=false) :
    ∃ L U, rowLower r=some L ∧ rowUpper r=some U ∧ L≤U ∧
      (∃ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ), (SMQLPatternRequests.blCharge p).1.natAbs=3 ∧
        SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
          (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d) ∧
        SMChargeDegreeBounds.twiceDimension n h d=U) ∧
      (∀ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ), (SMQLPatternRequests.blCharge p).1.natAbs=3 →
        SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
          (QLFiniteSupport.flavor (r.q : ZMod r.k) r.l) p h d) →
        L≤SMChargeDegreeBounds.twiceDimension n h d) := by
  have hi := row_intervals i r hr
  cases hl : rowLower r with
  | none => have := hi.1.mp hl; rw [ha] at this; contradiction
  | some L =>
    cases hu : rowUpper r with
    | none => have := hi.2.1.mp hu; rw [ha] at this; contradiction
    | some U =>
      refine ⟨L,U,rfl,rfl,hi.2.2 L (by simp [hl]) U (by simp [hu]),
        upper_attainment _ _ U hu,?_⟩
      intro n p h d hb ha'
      exact row_lower_bound r L hl p h d hb ha'

def exactCheck (r : Row) : Bool := r.b1Forbidden==false && rowLower r==rowUpper r
def exactCount : ℕ := (rows.filter exactCheck).length
def unresolvedCount : ℕ := (rows.filter (fun r => !r.b1Forbidden && !exactCheck r)).length

theorem interval_counts : exactCount=160 ∧ unresolvedCount=166 := by decide +kernel

theorem exact_check_semantics (i : Fin 11) (r : Row) [NeZero r.k]
    (hr : r ∈ batches i) (hc : exactCheck r=true) :
    ∃ M, rowLower r=some M ∧ IsMinimum (r.q : ZMod r.k) r.l 3 M := by
  have hh : r.b1Forbidden=false ∧ rowLower r=rowUpper r := by
    simpa [exactCheck] using hc
  obtain ⟨hflag,heq⟩ := hh
  obtain ⟨L,U,hl,hu,_,_,_⟩ := row_certificate i r hr hflag
  have he : L=U := by rw [hl,hu] at heq; exact Option.some.inj heq
  exact ⟨L,hl,row_exact r L hl (by simpa only [he] using hu)⟩

end Physics.SMB1MinimumClassification
