import Physics.StandardModel.Operators.SMFiniteHiggsSupport

/-! A finite table for the fixed three-generation universe. Species words
form a redundant finite superset of contents; no table entry is classified. -/
namespace GUT.SMFiniteSupportTable
set_option autoImplicit false
noncomputable section
open Math Representation BoundedHiggsSupport SMFiniteHiggsSupport
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

abbrev Pattern := (n : Fin 181) × (Fin n.val → DeltaLOneSignedInput.Species)
abbrev Index := Pattern × Fin 181 × Fin 181
instance : Fintype Pattern := inferInstance
instance : Fintype Index := inferInstance

abbrev TableTest (i : Index) :=
  Test flavor i.1.2 (i.2.1.val+i.2.2.val) ((i.2.1.val : ℤ)-i.2.2.val)

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem finite_universe_iff (h d : ℕ) (hn : n ≤ 180) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) ↔
      ∃ s t : Fin 181, s.val+t.val ≤ SMContentWeakBound.bound p ∧
        (h : ℤ)-d = (s.val : ℤ)-t.val ∧ Admissible h d (s.val+t.val) ∧
        SelectionCriteria.Allowed (Test flavor p (s.val+t.val) ((s.val : ℤ)-t.val)) := by
  rw [original_table_iff]
  have hb := SMContentWeakBound.bound_le_degree p
  constructor
  · rintro ⟨s,t,hsum,he,ha,ht⟩
    have hs := s.isLt
    have ht' := t.isLt
    exact ⟨⟨s.val,by omega⟩,⟨t.val,by omega⟩,hsum,he,ha,ht⟩
  · rintro ⟨s,t,hsum,he,ha,ht⟩
    exact ⟨⟨s.val,by omega⟩,⟨t.val,by omega⟩,hsum,he,ha,ht⟩

theorem all_degrees_iff (h d : ℕ) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) ↔
    n ≤ 180 ∧ ∃ s t : Fin 181, s.val+t.val ≤ SMContentWeakBound.bound p ∧
      (h : ℤ)-d = (s.val : ℤ)-t.val ∧ Admissible h d (s.val+t.val) ∧
      SelectionCriteria.Allowed (Test flavor p (s.val+t.val) ((s.val : ℤ)-t.val)) := by
  by_cases hn : n ≤ 180
  · simpa only [hn,true_and] using finite_universe_iff flavor p h d hn
  · have hf := original_degree_forbidden flavor p h d (by omega)
    rw [SelectionCriteria.forbidden_iff_not_allowed] at hf
    simp only [hf,hn,false_and]

def entry (hn : n ≤ 180) (s t : Fin 181) : Index :=
  (⟨⟨n,by omega⟩,p⟩,s,t)

theorem global_table_iff (h d : ℕ) (hn : n ≤ 180) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) ↔
      ∃ s t : Fin 181, s.val+t.val ≤ SMContentWeakBound.bound p ∧
        (h : ℤ)-d = (s.val : ℤ)-t.val ∧ Admissible h d (s.val+t.val) ∧
        SelectionCriteria.Allowed (TableTest flavor (entry p hn s t)) :=
  finite_universe_iff flavor p h d hn

theorem pilot_all_forbidden (h d : ℕ) :
    SelectionCriteria.Forbidden (OriginalSpace flavor SMContentWeakBound.pilot h d) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, original_charge_finite_iff]
  rintro ⟨hc,ht⟩
  have hy : SMContentWeakBound.hypercharge SMContentWeakBound.pilot = 2 := by decide
  rw [hy] at hc
  omega

theorem family_bound_controls :
    SMContentWeakBound.bound (![2,1,0,3] : Fin 4 → DeltaLOneSignedInput.Species) = 2 ∧
    SMContentWeakBound.bound (![0,0,1,4] : Fin 4 → DeltaLOneSignedInput.Species) = 2 ∧
    SMContentWeakBound.bound (![0,0,0,3] : Fin 4 → DeltaLOneSignedInput.Species) = 4 ∧
    SMContentWeakBound.bound (![2,1,1,4] : Fin 4 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.bound (![1,1,2,2,2,2] : Fin 6 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.bound (![3,3] : Fin 2 → DeltaLOneSignedInput.Species) = 2 := by decide

theorem family_charge_controls :
    SMContentWeakBound.hypercharge (![2,1,0,3] : Fin 4 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.hypercharge (![0,0,1,4] : Fin 4 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.hypercharge (![0,0,0,3] : Fin 4 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.hypercharge (![2,1,1,4] : Fin 4 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.hypercharge (![1,1,2,2,2,2] : Fin 6 → DeltaLOneSignedInput.Species) = 0 ∧
    SMContentWeakBound.hypercharge (![3,3] : Fin 2 → DeltaLOneSignedInput.Species) = -6 := by decide

end
end GUT.SMFiniteSupportTable
