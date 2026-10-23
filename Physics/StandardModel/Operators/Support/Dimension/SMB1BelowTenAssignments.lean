import Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTen

/-! Complete existing 572-assignment B1 classification below dimension ten.
Rows and their exhaustive identity coverage are the existing Lean domain. -/
namespace Physics.SMB1BelowTenAssignments
set_option autoImplicit false
open Math SMFiniteLeptonAssignments
open scoped BigOperators

def check (r : Row) : Bool := decide
  ((3 : ZMod r.k)*r.q+r.l=0 ∨ (3 : ZMod r.k)*r.q-r.l=0 ∨
    (3 : ZMod r.k)*r.q+3*r.l=0)

theorem row_allowed_iff (r : Row) [NeZero r.k] :
    SMB1BelowTen.Allowed (r.q : ZMod r.k) r.l ↔ check r=true := by
  rw [SMB1BelowTen.allowed_iff]
  simp only [check, decide_eq_true_eq]

theorem row_forbidden_iff (r : Row) [NeZero r.k] :
    SMB1BelowTen.Forbidden (r.q : ZMod r.k) r.l ↔ check r=false := by
  rw [SMB1BelowTen.forbidden_iff_not_allowed,row_allowed_iff]
  cases check r <;> decide

/-- Every row receives an actual original-space verdict, with no unknown case. -/
theorem row_decision (r : Row) [NeZero r.k] :
    if check r then SMB1BelowTen.Allowed (r.q : ZMod r.k) r.l
    else SMB1BelowTen.Forbidden (r.q : ZMod r.k) r.l := by
  cases he : check r
  · simpa only [he, Bool.false_eq_true, ite_false] using (row_forbidden_iff r).mpr he
  · simpa only [he, ite_true] using (row_allowed_iff r).mpr he

/-- The first congruence is excluded throughout the inherited assignment domain. -/
theorem domain_nonzero (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    (3 : ZMod r.k)*r.q+r.l≠0 := by
  have hd := (all_domain i r hr).2.2.2.2
  intro he
  have he' : ((3*r.q+r.l : ℕ) : ZMod r.k)=0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using he
  exact hd (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp he'))

theorem domain_allowed_iff (i : Fin 11) (r : Row) [NeZero r.k] (hr : r ∈ batches i) :
    SMB1BelowTen.Allowed (r.q : ZMod r.k) r.l ↔
      (3 : ZMod r.k)*r.q-r.l=0 ∨ (3 : ZMod r.k)*r.q+3*r.l=0 := by
  rw [SMB1BelowTen.allowed_iff]
  simp only [domain_nonzero i r hr, false_or]

def allowedCount : ℕ := (rows.filter check).length
def forbiddenCount : ℕ := (rows.filter (fun r => !check r)).length
def laterAllowedCount : ℕ :=
  (rows.filter (fun r => !check r && !r.b1Forbidden)).length
def allDegreeForbiddenCount : ℕ :=
  (rows.filter (fun r => !check r && r.b1Forbidden)).length

theorem counts : allowedCount=146 ∧ forbiddenCount=426 ∧
    laterAllowedCount=180 ∧ allDegreeForbiddenCount=246 := by
  decide +kernel

theorem exhaustive_count : allowedCount+forbiddenCount=rows.length := by
  obtain ⟨ha,hf,_,_⟩ := counts
  rw [ha,hf,rows_length]

/-- This is the inherited domain: each of the 572 triples occurs exactly once. -/
theorem coverage (k q l : ℕ)
    (hd : 2 ≤ k ∧ k ≤ 12 ∧ q < k ∧ l < k ∧ (3*q+l)%k≠0) :
    keys.count (k,q,l)=1 := unique_coverage k q l hd

theorem later_allowed_semantics (i : Fin 11) (r : Row) [NeZero r.k]
    (hr : r ∈ batches i) :
    (SMB1BelowTen.Forbidden (r.q : ZMod r.k) r.l ∧
      SMQLPatternRequests.OriginalAllowed (r.q : ZMod r.k) r.l
        (fun c => c.1.natAbs=3)) ↔ check r=false ∧ r.b1Forbidden=false :=
  and_congr (row_forbidden_iff r) (b1_allowed_iff i r hr)

theorem all_degree_forbidden_semantics (i : Fin 11) (r : Row) [NeZero r.k]
    (hr : r ∈ batches i) :
    (SMB1BelowTen.Forbidden (r.q : ZMod r.k) r.l ∧
      SMQLPatternRequests.OriginalForbidden (r.q : ZMod r.k) r.l
        (fun c => c.1.natAbs=3)) ↔ check r=false ∧ r.b1Forbidden=true :=
  and_congr (row_forbidden_iff r) (b1_forbidden_iff i r hr)

end Physics.SMB1BelowTenAssignments
