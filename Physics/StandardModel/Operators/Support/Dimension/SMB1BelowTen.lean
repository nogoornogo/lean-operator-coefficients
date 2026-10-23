import Physics.StandardModel.Operators.Support.Dimension.SMMinimumOperatorDimension

/-! Actual B1 coefficient support at engineering dimension strictly below ten.
The finite criterion retains both baryon signs and all Higgs bidegrees. -/
namespace Physics.SMB1BelowTen
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds
open scoped BigOperators

variable {k : ℕ} [NeZero k]

def Allowed (q l : ZMod k) : Prop :=
  ∃ (n : ℕ) (p : Fin n → Species) (h d : ℕ),
    (SMQLPatternRequests.blCharge p).1.natAbs=3 ∧
    twiceDimension n h d < 20 ∧
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)

def Forbidden (q l : ZMod k) : Prop :=
  ∀ (n : ℕ) (p : Fin n → Species) (h d : ℕ),
    (SMQLPatternRequests.blCharge p).1.natAbs=3 → twiceDimension n h d < 20 →
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)

theorem forbidden_iff_not_allowed (q l : ZMod k) : Forbidden q l ↔ ¬ Allowed q l := by
  simp only [Forbidden, Allowed, SelectionCriteria.forbidden_iff_not_allowed,
    not_exists, not_and]

/-- Only these normalized signed lepton charges can occur below ten. -/
theorem charge_candidates {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs=3)
    (hdim : twiceDimension n h d < 20)
    (hp : ((SMQLPatternRequests.blCharge p).1 + (SMQLPatternRequests.blCharge p).2)%2=0)
    (hy : SMContentWeakBound.hypercharge p + 3*((h : ℤ)-d)=0) :
    ((SMQLPatternRequests.blCharge p).1=3 ∧
      ((SMQLPatternRequests.blCharge p).2=1 ∨
       (SMQLPatternRequests.blCharge p).2= -1 ∨
       (SMQLPatternRequests.blCharge p).2=3)) ∨
    ((SMQLPatternRequests.blCharge p).1= -3 ∧
      ((SMQLPatternRequests.blCharge p).2= -1 ∨
       (SMQLPatternRequests.blCharge p).2=1 ∨
       (SMQLPatternRequests.blCharge p).2= -3)) := by
  have hc := charge_degree p
  have he := SMMinimumOperatorDimension.hypercharge_envelope p
  have habs : |(SMQLPatternRequests.blCharge p).1|=3 := by
    rw [← Int.natCast_natAbs, hb]
    rfl
  rw [habs] at hc
  have hl : |(SMQLPatternRequests.blCharge p).2| ≤ (n : ℤ)-3 := by omega
  rw [abs_le] at hl he
  rcases Int.natAbs_eq_iff.mp hb with hb | hb <;>
    unfold twiceDimension at hdim <;> omega

/-- Both signed branches use the actual input charge equation. -/
theorem necessary (q l : ZMod k) (ha : Allowed q l) :
    3*q+l=0 ∨ 3*q-l=0 ∨ 3*q+3*l=0 := by
  obtain ⟨n,p,h,d,hb,hd,ha⟩ := ha
  obtain ⟨hc,hy,_⟩ := (SMJointHiggsSupport.original_ql_iff p q l h d).mp ha
  rw [residual_linear] at hc
  have hp := original_parity q l p h d ha
  rcases charge_candidates p h d hb hd hp hy with ⟨hb,hl⟩ | ⟨hb,hl⟩ <;>
    rcases hl with hl | hl | hl <;> rw [hb,hl] at hc <;> push_cast at hc
  · exact Or.inl (by linear_combination hc)
  · exact Or.inr (Or.inl (by linear_combination hc))
  · exact Or.inr (Or.inr (by linear_combination hc))
  · exact Or.inl (by linear_combination -hc)
  · exact Or.inr (Or.inl (by linear_combination -hc))
  · exact Or.inr (Or.inr (by linear_combination -hc))

theorem plus_one_sufficient (q l : ZMod k) (hc : 3*q+l=0) : Allowed q l := by
  refine ⟨4,SMMinimumOperatorDimension.c1Pattern,0,0,by decide +kernel,by decide +kernel,?_⟩
  apply (SMJointHiggsSupport.original_ql_iff SMMinimumOperatorDimension.c1Pattern q l 0 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨0,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMMinimumOperatorDimension.c1Pattern=(3,1) := by decide +kernel
    rw [he]
    push_cast
    linear_combination hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMMinimumOperatorDimension.c1_counts]
    exact SMMinimumOperatorDimension.c1_support

theorem minus_one_sufficient (q l : ZMod k) (hc : 3*q-l=0) : Allowed q l := by
  refine ⟨4,SMLeptonChargeWitnesses.w3_n1_pattern,0,1,by decide +kernel,by decide +kernel,?_⟩
  apply (SMJointHiggsSupport.original_ql_iff SMLeptonChargeWitnesses.w3_n1_pattern q l 0 1).mpr
  refine ⟨?_,by decide +kernel,⟨⟨1,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMLeptonChargeWitnesses.w3_n1_pattern=(3,-1) := by decide +kernel
    rw [he]
    push_cast
    linear_combination hc
  · change BoundedHiggsSupport.Admissible 0 1 1
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMLeptonChargeWitnesses.w3_n1_counts_eq]
    exact SMLeptonChargeWitnesses.w3_n1_support

theorem plus_three_sufficient (q l : ZMod k) (hc : 3*q+3*l=0) : Allowed q l := by
  refine ⟨6,SMMinimumOperatorDimension.h1Pattern,0,0,by decide +kernel,by decide +kernel,?_⟩
  apply (SMJointHiggsSupport.original_ql_iff SMMinimumOperatorDimension.h1Pattern q l 0 0).mpr
  refine ⟨?_,by decide +kernel,⟨⟨0,by decide +kernel⟩,?_,?_⟩⟩
  · rw [residual_linear]
    have he : SMQLPatternRequests.blCharge SMMinimumOperatorDimension.h1Pattern=(3,3) := by decide +kernel
    rw [he]
    push_cast
    linear_combination hc
  · change BoundedHiggsSupport.Admissible 0 0 0
    unfold BoundedHiggsSupport.Admissible
    omega
  · rw [SMMinimumOperatorDimension.h1_counts]
    exact SMMinimumOperatorDimension.h1_support

theorem allowed_iff (q l : ZMod k) :
    Allowed q l ↔ 3*q+l=0 ∨ 3*q-l=0 ∨ 3*q+3*l=0 := by
  constructor
  · exact necessary q l
  · rintro (h | h | h)
    · exact plus_one_sufficient q l h
    · exact minus_one_sufficient q l h
    · exact plus_three_sufficient q l h

theorem forbidden_iff (q l : ZMod k) :
    Forbidden q l ↔ 3*q+l≠0 ∧ 3*q-l≠0 ∧ 3*q+3*l≠0 := by
  rw [forbidden_iff_not_allowed,allowed_iff]
  tauto

end Physics.SMB1BelowTen
