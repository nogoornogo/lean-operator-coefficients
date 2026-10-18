import GUT.SU6.SelectionRules.Models.ChargeProfileObstruction

namespace GUT.SU6FiniteIndexCertificate
set_option autoImplicit false
open scoped BigOperators
abbrev Label := ℤ × ℤ × ℤ × ℤ
/-- Pool order: 1,6,15,20,21,35,70; complete supplied SM profiles. -/
def branching : Fin 7 → List Label := ![[(0, 0, 0, 0)], [(0, 0, 0, 0), (0, 0, 1, 3), (1, 0, 0, (-2))], [(0, 0, 0, 6), (0, 0, 1, 3), (0, 1, 0, (-4)), (1, 0, 0, (-2)), (1, 0, 1, 1)], [(0, 0, 0, (-6)), (0, 0, 0, 6), (0, 1, 0, (-4)), (0, 1, 1, (-1)), (1, 0, 0, 4), (1, 0, 1, 1)], [(0, 0, 0, 0), (0, 0, 1, 3), (0, 0, 2, 6), (1, 0, 0, (-2)), (1, 0, 1, 1), (2, 0, 0, (-4))], [(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, (-3)), (0, 0, 1, 3), (0, 0, 2, 0), (0, 1, 0, 2), (0, 1, 1, 5), (1, 0, 0, (-2)), (1, 0, 1, (-5)), (1, 1, 0, 0)], [(0, 0, 0, 6), (0, 0, 1, 3), (0, 0, 1, 9), (0, 0, 2, 6), (0, 1, 0, (-4)), (0, 1, 1, (-1)), (1, 0, 0, (-2)), (1, 0, 0, 4), (1, 0, 1, 1), (1, 0, 1, 1), (1, 0, 2, 4), (1, 1, 0, (-6)), (2, 0, 0, (-4)), (2, 0, 1, (-1))]]
/-- Sparse index rows sufficient to separate all five targets. -/
def rows : Fin 7 → Fin 5 × Label := ![(0, (0, 0, 1, (-3))), (0, (0, 1, 0, (-4))), (0, (0, 1, 0, 2)), (0, (0, 1, 1, (-1))), (0, (2, 0, 0, (-4))), (1, (0, 0, 1, (-3))), (1, (0, 1, 0, 2))]
def conjugate (g : Label) : Label := (g.2.1,g.1,g.2.2.1,-g.2.2.2)
def column (r : Fin 7) (q : Fin 5) (i : Fin 7) : ℚ :=
  (if (rows i).1 = q then ((branching r).count (rows i).2 : ℚ) else 0) -
  (if (rows i).1.val = (5-q.val)%5 then
    ((branching r).count (conjugate (rows i).2) : ℚ) else 0)
/-- Three primitive row relations generate the five separating functionals. -/
def doubletDifference (i : Fin 7) : ℚ := if i = 0 then 1 else if i = 2 then -1 else 0
def tripletBalance (i : Fin 7) : ℚ := if i = 1 ∨ i = 3 ∨ i = 4 then 1 else 0
def chargedDifference (i : Fin 7) : ℚ := if i = 5 then -1 else if i = 6 then 1 else 0

def certificate (x : Fin 5) : Fin 7 → ℚ := match x with
  | 0 => -tripletBalance
  | 1 => chargedDifference
  | 2 => doubletDifference
  | 3 => -doubletDifference
  | 4 => tripletBalance

/-- Complete one-generation target labels in Q,U,D,L,E order. -/
def lightProfile : Fin 5 → List (Fin 5 × Label) := ![[(0, (1, 0, 1, 1)), (1, (0, 1, 0, (-4))), (4, (0, 1, 0, 2)), (1, (0, 0, 1, (-3))), (3, (0, 0, 0, 6))], [(1, (1, 0, 1, 1)), (2, (0, 1, 0, (-4))), (1, (0, 1, 0, 2)), (3, (0, 0, 1, (-3))), (4, (0, 0, 0, 6))], [(2, (1, 0, 1, 1)), (3, (0, 1, 0, (-4))), (3, (0, 1, 0, 2)), (0, (0, 0, 1, (-3))), (0, (0, 0, 0, 6))], [(3, (1, 0, 1, 1)), (4, (0, 1, 0, (-4))), (0, (0, 1, 0, 2)), (2, (0, 0, 1, (-3))), (1, (0, 0, 0, 6))], [(4, (1, 0, 1, 1)), (0, (0, 1, 0, (-4))), (2, (0, 1, 0, 2)), (4, (0, 0, 1, (-3))), (2, (0, 0, 0, 6))]]
def negateRow (row : Fin 5 × Label) : Fin 5 × Label :=
  (⟨(5-row.1.val)%5, Nat.mod_lt _ (by decide)⟩, conjugate row.2)
/-- The target is an output of the supplied complete light-profile dictionary. -/
def target (x : Fin 5) (i : Fin 7) : ℚ :=
  ((lightProfile x).count (rows i) : ℚ)-((lightProfile x).count (negateRow (rows i)) : ℚ)

theorem target_dictionary (x : Fin 5) (i : Fin 7) :
    target x i = ((lightProfile x).count (rows i) : ℚ) -
      ((lightProfile x).count (negateRow (rows i)) : ℚ) := rfl

/-- Multiplicities remain explicit supplied-profile counts, not an inferred
branching classification for arbitrary SU(6) representations. -/
def multiplicity (r : Fin 7) (g : Label) : ℚ := (branching r).count g

theorem doublet_count (r : Fin 7) :
    multiplicity r (0,0,1,-3) = multiplicity r (0,1,0,2) := by
  fin_cases r <;> norm_num [multiplicity, branching]

theorem conjugate_count (r : Fin 7) :
    multiplicity r (0,0,1,3) = multiplicity r (1,0,0,-2) := by
  fin_cases r <;> norm_num [multiplicity, branching]

theorem balance_count (r : Fin 7) :
    multiplicity r (0,1,0,-4)+multiplicity r (0,1,1,-1)+multiplicity r (2,0,0,-4) =
      multiplicity r (1,0,0,4)+multiplicity r (1,0,1,1)+multiplicity r (0,2,0,4) := by
  fin_cases r <;> norm_num [multiplicity, branching]

theorem row0_eq_row2 (r : Fin 7) (q : Fin 5) : column r q 0 = column r q 2 := by
  change ((if (0 : Fin 5) = q then multiplicity r (0,0,1,-3) else 0)-
    (if (0 : ℕ) = (5-q.val)%5 then multiplicity r (0,0,1,3) else 0)) =
    ((if (0 : Fin 5) = q then multiplicity r (0,1,0,2) else 0)-
    (if (0 : ℕ) = (5-q.val)%5 then multiplicity r (1,0,0,-2) else 0))
  rw [doublet_count, conjugate_count]

theorem row5_eq_row6 (r : Fin 7) (q : Fin 5) : column r q 5 = column r q 6 := by
  change ((if (1 : Fin 5) = q then multiplicity r (0,0,1,-3) else 0)-
    (if (1 : ℕ) = (5-q.val)%5 then multiplicity r (0,0,1,3) else 0)) =
    ((if (1 : Fin 5) = q then multiplicity r (0,1,0,2) else 0)-
    (if (1 : ℕ) = (5-q.val)%5 then multiplicity r (1,0,0,-2) else 0))
  rw [doublet_count, conjugate_count]

/-- Negating a cyclic charge preserves being zero. -/
theorem zero_neg_charge (q : Fin 5) : (0 : ℕ) = (5-q.val)%5 ↔ q = 0 := by
  constructor
  · intro h
    apply Fin.ext
    by_cases hz : q.val = 0
    · exact hz
    · have hlt : 5-q.val < 5 := by omega
      rw [Nat.mod_eq_of_lt hlt] at h
      have hq := q.isLt
      omega
  · intro h
    subst q
    norm_num

theorem row_balance (r : Fin 7) (q : Fin 5) :
    column r q 1+column r q 3+column r q 4 = 0 := by
  by_cases hq : q = 0
  · subst q
    change (multiplicity r (0,1,0,-4)-multiplicity r (1,0,0,4))+
      (multiplicity r (0,1,1,-1)-multiplicity r (1,0,1,1))+
      (multiplicity r (2,0,0,-4)-multiplicity r (0,2,0,4)) = 0
    have h := balance_count r
    linarith
  · have hp : (0 : Fin 5) ≠ q := Ne.symm hq
    have hn : ¬ (0 : ℕ) = (5-q.val)%5 := by
      rw [zero_neg_charge]
      exact hq
    simp [column, rows, hp, hn]

attribute [local irreducible] column

theorem annihilates (x : Fin 5) (r : Fin 7) (q : Fin 5) :
    ∑ i, certificate x i * column r q i = 0 := by
  have hA := row0_eq_row2 r q
  have hB := row_balance r q
  have hC := row5_eq_row6 r q
  fin_cases x <;>
    simp [certificate, doubletDifference, tripletBalance, chargedDifference, Fin.sum_univ_succ] <;>
    linarith

/-- Sparse response of each functional on arbitrary row data. -/
def response (x : Fin 5) (v : Fin 7 → ℚ) : ℚ := match x with
  | 0 => -(v 1+v 3+v 4)
  | 1 => -v 5+v 6
  | 2 => v 0-v 2
  | 3 => -v 0+v 2
  | 4 => v 1+v 3+v 4

theorem certificate_response (x : Fin 5) (v : Fin 7 → ℚ) :
    ∑ i, certificate x i*v i = response x v := by
  fin_cases x <;>
    simp [certificate, response, doubletDifference, tripletBalance, chargedDifference,
      Fin.sum_univ_succ] <;> ring

private theorem target_response0 : response 0 (target 0) = 1 := by
  change -(target 0 1+target 0 3+target 0 4) = 1
  norm_num [target, lightProfile, rows, negateRow, conjugate]

private theorem target_response1 : response 1 (target 1) = 1 := by
  change -target 1 5+target 1 6 = 1
  norm_num [target, lightProfile, rows, negateRow, conjugate]

private theorem target_response2 : response 2 (target 2) = 1 := by
  change target 2 0-target 2 2 = 1
  norm_num [target, lightProfile, rows, negateRow, conjugate]

private theorem target_response3 : response 3 (target 3) = 1 := by
  change -target 3 0+target 3 2 = 1
  norm_num [target, lightProfile, rows, negateRow, conjugate]

private theorem target_response4 : response 4 (target 4) = 1 := by
  change target 4 1+target 4 3+target 4 4 = 1
  norm_num [target, lightProfile, rows, negateRow, conjugate]

theorem separates (x : Fin 5) : ∑ i, certificate x i * target x i = 1 := by
  rw [certificate_response]
  fin_cases x
  · exact target_response0
  · exact target_response1
  · exact target_response2
  · exact target_response3
  · exact target_response4

/-- No rational copy coefficients can solve even these seven index rows. -/
theorem no_solution (x : Fin 5) (n : Fin 7 → Fin 5 → ℚ) :
    ¬ (∀ i, ∑ r, ∑ q, n r q * column r q i = target x i) := by
  intro h
  have he : (∑ i, certificate x i * (∑ r, ∑ q, n r q * column r q i)) = 1 := by
    simp_rw [h]
    exact separates x
  have hz : (∑ i, certificate x i * (∑ r, ∑ q, n r q * column r q i)) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro q _
    have hh : (∑ i, certificate x i * (n r q * column r q i)) =
        n r q * (∑ i, certificate x i * column r q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh, annihilates, mul_zero]
  rw [hz] at he
  norm_num at he

/-- Application input: an actual model must supply this necessary index transport. -/
def Admitted (x : Fin 5) : Prop :=
  ∃ n : Fin 7 → Fin 5 → ℚ, ∀ i, ∑ r, ∑ q, n r q * column r q i = target x i

theorem not_admitted (x : Fin 5) : ¬ Admitted x := by
  rintro ⟨n,h⟩
  exact no_solution x n h

/-- Signed integer coefficients already allow the negative conjugate columns. -/
theorem no_integer_solution (x : Fin 5) (n : Fin 7 → Fin 5 → ℤ) :
    ¬ (∀ i, ∑ r, ∑ q, (n r q : ℚ) * column r q i = target x i) :=
  no_solution x (fun r q => (n r q : ℚ))

end GUT.SU6FiniteIndexCertificate
