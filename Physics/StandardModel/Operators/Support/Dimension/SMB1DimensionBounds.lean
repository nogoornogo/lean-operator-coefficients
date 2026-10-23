import Physics.StandardModel.Operators.Support.Dimension.SMB1BelowTenAssignments
import Physics.StandardModel.Operators.Support.Coordinates.SMChiralitySupport

/-! Signed-charge engineering-dimension bounds on actual B1 coefficients. -/
namespace Physics.SMB1DimensionBounds
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds SMFiniteLeptonSupport
open scoped BigOperators

theorem species_grade_identity (s : Species) :
    (1 : ZMod 4)-2*(hypercharge s : ZMod 4)-(baryon s : ZMod 4)-
      (lepton s : ZMod 4)=2*(SMChiralitySupport.slotCount false s : ZMod 4) := by
  fin_cases s <;> decide +kernel

theorem grade_identity {n : ℕ} (p : Fin n → Species) :
    (n : ZMod 4)-2*(SMContentWeakBound.hypercharge p : ZMod 4)-
      ((SMQLPatternRequests.blCharge p).1 : ZMod 4)-
      ((SMQLPatternRequests.blCharge p).2 : ZMod 4)=
        2*(SMChiralitySupport.count p false : ZMod 4) := by
  have he := congrArg (fun f : Fin n → ZMod 4 => ∑ i, f i)
    (funext (fun i => species_grade_identity (p i)))
  simpa [SMContentWeakBound.hypercharge,SMQLPatternRequests.blCharge,
    SMChiralitySupport.count,Finset.sum_sub_distrib,Finset.mul_sum] using he

theorem original_left_even {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    SMChiralitySupport.count p false % 2=0 := by
  by_contra hn
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMChiralitySupport.original_forbidden (QLFiniteSupport.flavor q l) p false hn h d) ha

/-- Necessary engineering-grade congruence from actual independent chirality. -/
theorem original_grade_congruence {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    ((twiceDimension n h d : ℤ)-3*(SMQLPatternRequests.blCharge p).1+
      (SMQLPatternRequests.blCharge p).2)%4=0 := by
  have he := grade_identity p
  have hl := original_left_even q l p h d ha
  have hz : (2*(SMChiralitySupport.count p false) : ℕ)%4=0 := by omega
  have hz' : (2 : ZMod 4)*(SMChiralitySupport.count p false : ZMod 4)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (ZMod.natCast_eq_zero_iff _ 4).mpr (Nat.dvd_of_mod_eq_zero hz)
  rw [hz'] at he
  have hi : (((n : ℤ)-2*SMContentWeakBound.hypercharge p-
      (SMQLPatternRequests.blCharge p).1-(SMQLPatternRequests.blCharge p).2 : ℤ) : ZMod 4)=0 := by
    simpa only [Int.cast_sub,Int.cast_natCast,Int.cast_mul,Int.cast_ofNat] using he
  have hm := Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hi)
  have hy := ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).2.1
  unfold twiceDimension
  omega

/-- Conservative charge lower grade, retained after the weak-envelope resource stop. -/
def lowerGrade (L : ℤ) : ℕ := 3*(3+L.natAbs)

/-- Existing charge bounds with the same signed-normalized candidate. -/
theorem original_lower {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    ∃ L ∈ leptonRange 3, (3 : ZMod k)*q+(L : ZMod k)*l=0 ∧
      lowerGrade L ≤ twiceDimension n h d := by
  obtain ⟨L,hL,he⟩ := SMFiniteLeptonDegreeBounds.normalized_content 3 q l p h d hb ha
  obtain ⟨hr,hq⟩ := Finset.mem_filter.mp hL
  refine ⟨L,hr,hq,?_⟩
  have hn := selected_degree p 3 hb
  have hz := Int.natCast_natAbs (SMQLPatternRequests.blCharge p).2
  unfold lowerGrade twiceDimension
  omega

end Physics.SMB1DimensionBounds
