import Physics.StandardModel.Operators.SMB1WeakDimensionBounds

/-! Strengthened signed-charge grades, separated from support extraction. -/
namespace GUT.SMB1StrongDimensionBounds
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds SMFiniteLeptonSupport
open SMB1DimensionBounds SMB1WeakDimensionBounds
open scoped BigOperators

/-- The charge/hypercharge lower grade before the chirality congruence. -/
def rawLower (L : ℤ) : ℕ :=
  max (max (3*(3+L.natAbs)) ((3+L.natAbs)+2*(2*L-1).natAbs))
    (max (7*L-15).toNat (-7*L-9).toNat)

/-- Enforce the engineering-grade congruence as well as the two inequalities. -/
def lowerGrade (L : ℤ) : ℕ :=
  if ((rawLower L : ℤ)+L-1)%4=0 then rawLower L else rawLower L+2

private theorem arithmetic_positive (n h d : ℕ) (L Y : ℤ)
    (hc : 3+|L| ≤ (n : ℤ)) (he : |Y-3+6*L| ≤ 3*(n : ℤ))
    (hw : |7*L-3| ≤ 12+(twiceDimension n h d : ℤ))
    (hy : Y+3*((h : ℤ)-d)=0) (hp : (3+L)%2=0)
    (hg : ((twiceDimension n h d : ℤ)-9+L)%4=0)
    (hL : |L|≤18) : lowerGrade L ≤ twiceDimension n h d := by
  rw [abs_le] at hL
  have hbnd : -17 ≤ L ∧ L≤17 := by omega
  obtain ⟨hlo,hhi⟩ := hbnd
  rw [abs_le] at he hw
  interval_cases L <;> norm_num [lowerGrade,rawLower] at * <;>
    unfold twiceDimension at * <;> omega

private theorem arithmetic_negative (n h d : ℕ) (L Y : ℤ)
    (hc : 3+|L| ≤ (n : ℤ)) (he : |Y+3+6*L| ≤ 3*(n : ℤ))
    (hw : |7*L+3| ≤ 12+(twiceDimension n h d : ℤ))
    (hy : Y+3*((h : ℤ)-d)=0) (hp : (-3+L)%2=0)
    (hg : ((twiceDimension n h d : ℤ)+9+L)%4=0)
    (hL : |L|≤18) : lowerGrade (-L) ≤ twiceDimension n h d := by
  rw [abs_le] at hL
  have hbnd : -17 ≤ L ∧ L≤17 := by omega
  obtain ⟨hlo,hhi⟩ := hbnd
  rw [abs_le] at he hw
  interval_cases L <;> norm_num [lowerGrade,rawLower] at * <;>
    unfold twiceDimension at * <;> omega

/-- Normalize both charges while retaining the actual input's engineering grade. -/
theorem original_lower {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    ∃ L ∈ leptonRange 3, (3 : ZMod k)*q+(L : ZMod k)*l=0 ∧
      lowerGrade L ≤ twiceDimension n h d := by
  have hc := charge_degree p
  have he := SMMinimumOperatorDimension.hypercharge_envelope p
  have hw := SMB1WeakDimensionBounds.original_weak_envelope q l p h d ha
  have hy := ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).2.1
  have hp := original_parity q l p h d ha
  have hg := SMB1DimensionBounds.original_grade_congruence q l p h d ha
  have hL := original_lepton_capacity q l p h d ha
  have hq := (residual_linear q l p).symm.trans
    ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).1
  have hB : |(SMQLPatternRequests.blCharge p).1|=3 := by
    rw [← Int.natCast_natAbs,hb]
    rfl
  rw [hB] at hc
  rcases Int.natAbs_eq_iff.mp hb with hb | hb
  · refine ⟨(SMQLPatternRequests.blCharge p).2,(mem_range 3 _).mpr ⟨hL,by omega⟩,?_,?_⟩
    · simpa [hb] using hq
    · rw [hb] at he hw hg
      exact arithmetic_positive n h d _ _ hc he hw hy (by omega) (by simpa using hg) hL
  · refine ⟨-(SMQLPatternRequests.blCharge p).2,
      (mem_range 3 _).mpr ⟨by simpa using hL,by omega⟩,?_,?_⟩
    · rw [hb] at hq
      push_cast at hq ⊢
      linear_combination -hq
    · rw [hb] at he hw hg
      exact arithmetic_negative n h d _ _ hc (by simpa using he) (by simpa using hw)
        hy (by omega) (by simpa using hg) hL

end GUT.SMB1StrongDimensionBounds
