import Physics.StandardModel.Operators.Support.Quark.SMQLCompactMultiplicity
import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteSupportTable
import Physics.StandardModel.Operators.Selection.ProhibitionPatterns
import Math.LinearAlgebra.Selection.MixedSelectionRequests

/-! A finite actual-coefficient request facade for fixed-input scalar q/l
symmetries. Forbidden targets use universal tests; each allowed target needs
its own witness. The original all-degree coefficient semantics are proved. -/
namespace Physics.SMQLPatternRequests
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria
abbrev Index := SMFiniteSupportTable.Index

def Valid (i : Index) : Prop := i.2.1.val+i.2.2.val ≤ SMContentWeakBound.bound i.1.2

def blCharge {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) : ℤ × ℤ :=
  (∑ j, DeltaLOneSignedInput.baryon (p j),∑ j, DeltaLOneSignedInput.lepton (p j))

theorem selector_matches_existing (select : ℤ × ℤ → Prop) {n m : ℕ}
    (p : Fin n → DeltaLOneSignedInput.Species) (s : Fin m → BnvMixedInput.ScalarSpecies) :
    (ComposableBLSupport.specification select).test n m p s ↔ select (blCharge p) := by
  change select (MixedChargeSelection.charge ComposableBLSupport.fermionCharge ComposableBLSupport.bosonCharge p s) ↔ _
  rw [ComposableBLSupport.charge_eq]
  rfl

def Entries (select : ℤ × ℤ → Prop) := {i : Index // Valid i ∧ select (blCharge i.1.2)}
instance (select : ℤ × ℤ → Prop) : Fintype (Entries select) := by
  classical
  unfold Entries
  infer_instance

variable {k : ℕ} [NeZero k] (q l : ZMod k)

abbrev Coefficients (select : ℤ × ℤ → Prop) :=
  ∀ i : Entries select, SMFiniteSupportTable.TableTest (QLFiniteSupport.flavor q l) i.val

def OriginalAllowed (select : ℤ × ℤ → Prop) : Prop :=
  ∃ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ), select (blCharge p) ∧
    Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)

def OriginalForbidden (select : ℤ × ℤ → Prop) : Prop :=
  ∀ (n : ℕ) (p : Fin n → DeltaLOneSignedInput.Species) (h d : ℕ), select (blCharge p) →
    Forbidden (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)

theorem entry_original (i : Index) (hv : Valid i)
    (ha : Allowed (SMFiniteSupportTable.TableTest (QLFiniteSupport.flavor q l) i)) :
    Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) i.1.2 i.2.1.val i.2.2.val) := by
  apply (SMFiniteHiggsSupport.original_allowed_iff (QLFiniteSupport.flavor q l) i.1.2 _ _).mpr
  refine ⟨⟨i.2.1.val+i.2.2.val,Nat.lt_succ_of_le hv⟩,?_,ha⟩
  change BoundedHiggsSupport.Admissible i.2.1.val i.2.2.val (i.2.1.val+i.2.2.val)
  unfold BoundedHiggsSupport.Admissible
  omega

theorem allowed_iff_original (select : ℤ × ℤ → Prop) :
    Allowed (Coefficients q l select) ↔ OriginalAllowed q l select := by
  rw [SelectionCriteria.allowed_family]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val.1.1.val,i.val.1.2,i.val.2.1.val,i.val.2.2.val,i.property.2,
      entry_original q l i.val i.property.1 hi⟩
  · rintro ⟨n,p,h,d,hselect,ha⟩
    obtain ⟨hn,s,t,hbound,_,_,ht⟩ :=
      (SMFiniteSupportTable.all_degrees_iff (QLFiniteSupport.flavor q l) p h d).mp ha
    exact ⟨⟨SMFiniteSupportTable.entry p hn s t,⟨hbound,hselect⟩⟩,ht⟩

theorem forbidden_iff_original (select : ℤ × ℤ → Prop) :
    Forbidden (Coefficients q l select) ↔ OriginalForbidden q l select := by
  rw [forbidden_iff_not_allowed,allowed_iff_original]
  simp only [OriginalAllowed,OriginalForbidden,not_exists,not_and,← forbidden_iff_not_allowed]

def EntryAllowed (i : Index) : Prop :=
  QLFiniteSupport.charge q l i.1.2 = 0 ∧
    0 < SMQLCompactMultiplicity.multiplicity q l i.1.2 (i.2.1.val+i.2.2.val) ((i.2.1.val : ℤ)-i.2.2.val)

abbrev ReductionInput := ∀ i : Index, Valid i → SMQLCompactMultiplicity.Input q l i.1.2
  (i.2.1.val+i.2.2.val) ((i.2.1.val : ℤ)-i.2.2.val)

theorem entry_allowed_iff (i : Index) (hv : Valid i) (input : ReductionInput q l) :
    Allowed (SMFiniteSupportTable.TableTest (QLFiniteSupport.flavor q l) i) ↔ EntryAllowed q l i :=
  SMQLCompactMultiplicity.test_allowed_iff q l i.1.2 _ _ (input i hv)

theorem allowed_iff (select : ℤ × ℤ → Prop) (input : ReductionInput q l) :
    Allowed (Coefficients q l select) ↔ ∃ i : Entries select, EntryAllowed q l i.val := by
  rw [SelectionCriteria.allowed_family]
  exact exists_congr (fun i => entry_allowed_iff q l i.val i.property.1 input)

theorem forbidden_iff (select : ℤ × ℤ → Prop) (input : ReductionInput q l) :
    Forbidden (Coefficients q l select) ↔ ∀ i : Entries select, ¬ EntryAllowed q l i.val := by
  rw [forbidden_iff_not_allowed,allowed_iff q l select input]
  exact not_exists

/-- A direct charge exclusion does not require the external Weyl input. -/
theorem forbid_of_charge (select : ℤ × ℤ → Prop)
    (hcharge : ∀ i : Entries select, QLFiniteSupport.charge q l i.val.1.2 ≠ 0) :
    Forbidden (Coefficients q l select) := by
  rw [forbidden_iff_not_allowed,SelectionCriteria.allowed_family]
  rintro ⟨i,hi⟩
  exact hcharge i ((QLFiniteSupport.test_allowed_iff q l i.val.1.2 _ _).mp hi).1

abbrev Target := ProhibitionPatterns.BLTarget
abbrev Domain (t : Target) := Coefficients q l (ProhibitionPatterns.target t)
abbrev Request := MixedSelectionRequests.Request Target
abbrev Satisfies (request : Request) := MixedSelectionRequests.Satisfies (Domain q l) request

def Conditions (request : Request) : Prop :=
  (∀ t ∈ request.forbid, ∀ i : Entries (ProhibitionPatterns.target t), ¬ EntryAllowed q l i.val) ∧
  (∀ t ∈ request.allow, ∃ i : Entries (ProhibitionPatterns.target t), EntryAllowed q l i.val)

theorem satisfies_iff (request : Request) (input : ReductionInput q l) :
    Satisfies q l request ↔ Conditions q l request := by
  unfold Satisfies MixedSelectionRequests.Satisfies Conditions
  exact and_congr (forall_congr' (fun t => forall_congr' (fun _ => forbidden_iff q l _ input)))
    (forall_congr' (fun t => forall_congr' (fun _ => allowed_iff q l _ input)))

theorem original_request_iff (request : Request) : Satisfies q l request ↔
    (∀ t ∈ request.forbid, OriginalForbidden q l (ProhibitionPatterns.target t)) ∧
    (∀ t ∈ request.allow, OriginalAllowed q l (ProhibitionPatterns.target t)) := by
  unfold Satisfies MixedSelectionRequests.Satisfies
  exact and_congr (forall_congr' (fun t => forall_congr' (fun _ => forbidden_iff_original q l _)))
    (forall_congr' (fun t => forall_congr' (fun _ => allowed_iff_original q l _)))

/-- Data specifying B1 prohibition and B2 allowance; no model witness is asserted. -/
def b1ForbiddenB2Allowed : Request := ⟨{.bOne},{.bTwo}⟩

theorem b1_b2_iff (input : ReductionInput q l) : Satisfies q l b1ForbiddenB2Allowed ↔
    (∀ i : Entries (ProhibitionPatterns.target .bOne), ¬ EntryAllowed q l i.val) ∧
    (∃ i : Entries (ProhibitionPatterns.target .bTwo), EntryAllowed q l i.val) := by
  rw [satisfies_iff q l _ input]
  simp only [Conditions,b1ForbiddenB2Allowed,Set.mem_singleton_iff,forall_eq]

theorem b1_b2_original_iff : Satisfies q l b1ForbiddenB2Allowed ↔
    OriginalForbidden q l (ProhibitionPatterns.target .bOne) ∧
    OriginalAllowed q l (ProhibitionPatterns.target .bTwo) := by
  rw [original_request_iff]
  simp only [b1ForbiddenB2Allowed,Set.mem_singleton_iff,forall_eq]

theorem allow_of_entry (t : Target) (i : Entries (ProhibitionPatterns.target t))
    (input : ReductionInput q l) (hi : EntryAllowed q l i.val) : Allowed (Domain q l t) :=
  (allowed_iff q l _ input).mpr ⟨i,hi⟩

end
end Physics.SMQLPatternRequests
