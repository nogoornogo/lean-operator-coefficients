import Physics.StandardModel.Operators.Support.Coordinates.SMContentCapacity
import Physics.StandardModel.Operators.Support.Dimension.SMChargeDegreeBounds
import Physics.StandardModel.Operators.Support.Lepton.SMLeptonChargeWitnesses

/-! Finite lepton-charge capacity/parity constraints on the actual original
coefficient spaces. The range is initially an outer bound, not a support test. -/
namespace Physics.SMFiniteLeptonSupport
set_option autoImplicit false
open Math DeltaLOneSignedInput SMChargeDegreeBounds
open scoped BigOperators

theorem sum_by_species {n : ℕ} (p : Fin n → Species) (w : Species → ℤ) :
    ∑ i, w (p i) = ∑ s, (SMIteratedContent.counts p s : ℤ)*w s := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun i (_ : i ∈ Finset.univ) =>
    Finset.mem_univ (p i)) w]
  simp [SMIteratedContent.counts, Finset.sum_const]

theorem lepton_counts {n : ℕ} (p : Fin n → Species) :
    (SMQLPatternRequests.blCharge p).2 =
      (SMIteratedContent.counts p 3 : ℤ) + SMIteratedContent.counts p 4 -
        SMIteratedContent.counts p 8 - SMIteratedContent.counts p 9 := by
  change (∑ i, lepton (p i)) = _
  rw [sum_by_species]
  simp [lepton, Fin.sum_univ_succ]
  ring

theorem original_fits {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    SMContentCapacity.Fits p := by
  by_contra hc
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMContentCapacity.original_ql_forbidden p q l h d hc) ha

theorem lepton_capacity {n : ℕ} (p : Fin n → Species) (hc : SMContentCapacity.Fits p) :
    |(SMQLPatternRequests.blCharge p).2| ≤ 18 := by
  have h3 := hc 3
  have h4 := hc 4
  have h8 := hc 8
  have h9 := hc 9
  rw [SMConstantWeakCapacity.dimension_eq] at h3 h4 h8 h9
  norm_num at h3 h4 h8 h9
  rw [lepton_counts]
  rw [abs_le]
  constructor <;> omega

theorem original_lepton_capacity {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    |(SMQLPatternRequests.blCharge p).2| ≤ 18 :=
  lepton_capacity p (original_fits q l p h d ha)

/-- Candidate lepton charges after normalizing the sign of baryon charge. -/
def leptonRange (b : ℕ) : Finset ℤ :=
  (Finset.Icc (-18) 18).filter (fun L => ((b : ℤ)+L)%2=0)

theorem mem_range (b : ℕ) (L : ℤ) :
    L ∈ leptonRange b ↔ |L|≤18 ∧ ((b : ℤ)+L)%2=0 := by
  simp only [leptonRange, Finset.mem_filter, Finset.mem_Icc, abs_le]

theorem range_card : (leptonRange 3).card=18 ∧ (leptonRange 6).card=19 := by
  decide +kernel

theorem b1_lepton_bound (L : ℤ) (hL : L ∈ leptonRange 3) : |L|≤17 := by
  obtain ⟨hbound,hpar⟩ := (mem_range 3 L).mp hL
  rw [abs_le] at hbound ⊢
  constructor <;> omega

/-- Negative B3 is handled by negating both charges in the scalar equation;
no unproved conjugate-source transport is used. -/
theorem normalize {k : ℕ} (q l : ZMod k) (b : ℕ) (B L : ℤ)
    (hb : B.natAbs=b) (hp : (B+L)%2=0) (hl : |L|≤18)
    (hc : (B : ZMod k)*q + (L : ZMod k)*l=0) :
    ∃ z ∈ leptonRange b, (b : ZMod k)*q + (z : ZMod k)*l=0 := by
  rcases Int.natAbs_eq_iff.mp hb with hb | hb
  · refine ⟨L, (mem_range b L).mpr ⟨hl, ?_⟩, ?_⟩
    · simpa only [hb] using hp
    · simpa only [hb, Int.cast_natCast] using hc
  · refine ⟨-L, (mem_range b (-L)).mpr ⟨by simpa only [abs_neg] using hl, ?_⟩, ?_⟩
    · omega
    · rw [hb] at hc
      push_cast at hc ⊢
      linear_combination -hc

theorem original_necessary {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ)
    (ha : SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=b)) :
    ∃ L ∈ leptonRange b, (b : ZMod k)*q + (L : ZMod k)*l=0 := by
  obtain ⟨n,p,h,d,hb,ha⟩ := ha
  apply normalize q l b _ _ hb (original_parity q l p h d ha)
    (original_lepton_capacity q l p h d ha)
  exact (residual_linear q l p).symm.trans
    ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).1


open SMLeptonChargeWitnesses

/-- All capacity/parity candidates at B3=3/6 have explicit actual support. -/
theorem original_sufficient {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ)
    (hb : b=3 ∨ b=6) (L : ℤ) (hL : L ∈ leptonRange b)
    (hc : (b : ZMod k)*q + (L : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=b) := by
  rcases hb with rfl | rfl
  · have hv := (mem_range 3 L).mp hL
    obtain ⟨hlo,hhi⟩ := abs_le.mp hv.1
    interval_cases L <;> norm_num at hv
    · exact w3_n17_neutral q l (by simpa using hc)
    · exact w3_n15_neutral q l (by simpa using hc)
    · exact w3_n13_neutral q l (by simpa using hc)
    · exact w3_n11_neutral q l (by simpa using hc)
    · exact w3_n9_neutral q l (by simpa using hc)
    · exact w3_n7_neutral q l (by simpa using hc)
    · exact w3_n5_neutral q l (by simpa using hc)
    · exact w3_n3_neutral q l (by simpa using hc)
    · exact w3_n1_neutral q l (by simpa using hc)
    · exact w3_p1_neutral q l (by simpa using hc)
    · exact w3_p3_neutral q l (by simpa using hc)
    · exact w3_p5_neutral q l (by simpa using hc)
    · exact w3_p7_neutral q l (by simpa using hc)
    · exact w3_p9_neutral q l (by simpa using hc)
    · exact w3_p11_neutral q l (by simpa using hc)
    · exact w3_p13_neutral q l (by simpa using hc)
    · exact w3_p15_neutral q l (by simpa using hc)
    · exact w3_p17_neutral q l (by simpa using hc)
  · have hv := (mem_range 6 L).mp hL
    obtain ⟨hlo,hhi⟩ := abs_le.mp hv.1
    interval_cases L <;> norm_num at hv
    · exact w6_n18_neutral q l (by simpa using hc)
    · exact w6_n16_neutral q l (by simpa using hc)
    · exact w6_n14_neutral q l (by simpa using hc)
    · exact w6_n12_neutral q l (by simpa using hc)
    · exact w6_n10_neutral q l (by simpa using hc)
    · exact w6_n8_neutral q l (by simpa using hc)
    · exact w6_n6_neutral q l (by simpa using hc)
    · exact w6_n4_neutral q l (by simpa using hc)
    · exact w6_n2_neutral q l (by simpa using hc)
    · exact w6_p0_neutral q l (by simpa using hc)
    · exact w6_p2_neutral q l (by simpa using hc)
    · exact w6_p4_neutral q l (by simpa using hc)
    · exact w6_p6_neutral q l (by simpa using hc)
    · exact w6_p8_neutral q l (by simpa using hc)
    · exact w6_p10_neutral q l (by simpa using hc)
    · exact w6_p12_neutral q l (by simpa using hc)
    · exact w6_p14_neutral q l (by simpa using hc)
    · exact w6_p16_neutral q l (by simpa using hc)
    · exact w6_p18_neutral q l (by simpa using hc)

theorem exact_sufficient {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ)
    (hb : b=3 ∨ b=6) (L : ℤ) (hL : L ∈ leptonRange b)
    (hc : (b : ZMod k)*q + (L : ZMod k)*l=0) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=((b : ℤ),L)) := by
  rcases hb with rfl | rfl
  · have hv := (mem_range 3 L).mp hL
    obtain ⟨hlo,hhi⟩ := abs_le.mp hv.1
    interval_cases L <;> norm_num at hv
    · exact w3_n17_exact q l (by simpa using hc)
    · exact w3_n15_exact q l (by simpa using hc)
    · exact w3_n13_exact q l (by simpa using hc)
    · exact w3_n11_exact q l (by simpa using hc)
    · exact w3_n9_exact q l (by simpa using hc)
    · exact w3_n7_exact q l (by simpa using hc)
    · exact w3_n5_exact q l (by simpa using hc)
    · exact w3_n3_exact q l (by simpa using hc)
    · exact w3_n1_exact q l (by simpa using hc)
    · exact w3_p1_exact q l (by simpa using hc)
    · exact w3_p3_exact q l (by simpa using hc)
    · exact w3_p5_exact q l (by simpa using hc)
    · exact w3_p7_exact q l (by simpa using hc)
    · exact w3_p9_exact q l (by simpa using hc)
    · exact w3_p11_exact q l (by simpa using hc)
    · exact w3_p13_exact q l (by simpa using hc)
    · exact w3_p15_exact q l (by simpa using hc)
    · exact w3_p17_exact q l (by simpa using hc)
  · have hv := (mem_range 6 L).mp hL
    obtain ⟨hlo,hhi⟩ := abs_le.mp hv.1
    interval_cases L <;> norm_num at hv
    · exact w6_n18_exact q l (by simpa using hc)
    · exact w6_n16_exact q l (by simpa using hc)
    · exact w6_n14_exact q l (by simpa using hc)
    · exact w6_n12_exact q l (by simpa using hc)
    · exact w6_n10_exact q l (by simpa using hc)
    · exact w6_n8_exact q l (by simpa using hc)
    · exact w6_n6_exact q l (by simpa using hc)
    · exact w6_n4_exact q l (by simpa using hc)
    · exact w6_n2_exact q l (by simpa using hc)
    · exact w6_p0_exact q l (by simpa using hc)
    · exact w6_p2_exact q l (by simpa using hc)
    · exact w6_p4_exact q l (by simpa using hc)
    · exact w6_p6_exact q l (by simpa using hc)
    · exact w6_p8_exact q l (by simpa using hc)
    · exact w6_p10_exact q l (by simpa using hc)
    · exact w6_p12_exact q l (by simpa using hc)
    · exact w6_p14_exact q l (by simpa using hc)
    · exact w6_p16_exact q l (by simpa using hc)
    · exact w6_p18_exact q l (by simpa using hc)

theorem exact_original_iff {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ)
    (hb : b=3 ∨ b=6) (L : ℤ) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c=((b : ℤ),L)) ↔
      L ∈ leptonRange b ∧ (b : ZMod k)*q + (L : ZMod k)*l=0 := by
  constructor
  · rintro ⟨n,p,h,d,hc,ha⟩
    have hl := original_lepton_capacity q l p h d ha
    have hp := original_parity q l p h d ha
    have hr := (residual_linear q l p).symm.trans
      ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).1
    rw [hc] at hl hp hr
    exact ⟨(mem_range b L).mpr ⟨hl,hp⟩, by simpa using hr⟩
  · rintro ⟨hL,hc⟩
    exact exact_sufficient q l b hb L hL hc

/-- Finite exact charge criterion, uniform in the nonzero cyclic modulus. -/
theorem original_allowed_iff {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ)
    (hb : b=3 ∨ b=6) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=b) ↔
      ∃ L ∈ leptonRange b, (b : ZMod k)*q + (L : ZMod k)*l=0 := by
  constructor
  · exact original_necessary q l b
  · rintro ⟨L,hL,hc⟩
    exact original_sufficient q l b hb L hL hc

theorem original_forbidden_iff {k : ℕ} [NeZero k] (q l : ZMod k) (b : ℕ)
    (hb : b=3 ∨ b=6) :
    SMQLPatternRequests.OriginalForbidden q l (fun c => c.1.natAbs=b) ↔
      ∀ L ∈ leptonRange b, (b : ZMod k)*q + (L : ZMod k)*l≠0 := by
  rw [← SMQLPatternRequests.forbidden_iff_original,
    SelectionCriteria.forbidden_iff_not_allowed, SMQLPatternRequests.allowed_iff_original,
    original_allowed_iff q l b hb]
  simp only [not_exists, not_and]

theorem b1_allowed_iff {k : ℕ} [NeZero k] (q l : ZMod k) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=3) ↔
      ∃ L ∈ leptonRange 3, (3 : ZMod k)*q + (L : ZMod k)*l=0 :=
  original_allowed_iff q l 3 (Or.inl rfl)

theorem b2_allowed_iff {k : ℕ} [NeZero k] (q l : ZMod k) :
    SMQLPatternRequests.OriginalAllowed q l (fun c => c.1.natAbs=6) ↔
      ∃ L ∈ leptonRange 6, (6 : ZMod k)*q + (L : ZMod k)*l=0 :=
  original_allowed_iff q l 6 (Or.inr rfl)

/-- Same combined request as the existing original-space facade. -/
theorem b1_b2_iff {k : ℕ} [NeZero k] (q l : ZMod k) :
    SMQLPatternRequests.Satisfies q l SMQLPatternRequests.b1ForbiddenB2Allowed ↔
      (∀ L ∈ leptonRange 3, (3 : ZMod k)*q + (L : ZMod k)*l≠0) ∧
      (∃ L ∈ leptonRange 6, (6 : ZMod k)*q + (L : ZMod k)*l=0) := by
  rw [SMQLPatternRequests.b1_b2_original_iff]
  exact and_congr (original_forbidden_iff q l 3 (Or.inl rfl)) (b2_allowed_iff q l)

end Physics.SMFiniteLeptonSupport
