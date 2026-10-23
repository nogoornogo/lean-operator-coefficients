import Physics.StandardModel.Operators.Support.Quark.SMQLPatternRequests
import Physics.StandardModel.Operators.Selection.InverseLeptonParitySelection
import Physics.StandardModel.Operators.Support.Joint.SMJointHiggsSupport

/-! Charge bounds on fermion degree. Twice the four-dimensional engineering
dimension is a grading convention; no anomalous dimensions or rates enter. -/
namespace Physics.SMChargeDegreeBounds
set_option autoImplicit false
open Math DeltaLOneSignedInput
open scoped BigOperators

theorem species_abs (s : Species) : |baryon s| + |lepton s| = 1 := by
  fin_cases s <;> simp [baryon, lepton]

/-- Quarks and leptons occupy disjoint signed species. -/
theorem charge_degree {n : ℕ} (p : Fin n → Species) :
    |(SMQLPatternRequests.blCharge p).1| + |(SMQLPatternRequests.blCharge p).2| ≤ (n : ℤ) := by
  change |∑ i, baryon (p i)| + |∑ i, lepton (p i)| ≤ _
  calc
    _ ≤ (∑ i, |baryon (p i)|) + ∑ i, |lepton (p i)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, (|baryon (p i)| + |lepton (p i)|) := Finset.sum_add_distrib.symm
    _ = (n : ℤ) := by simp [species_abs]

theorem selected_degree {n : ℕ} (p : Fin n → Species) (b : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = b) :
    (b : ℤ) + |(SMQLPatternRequests.blCharge p).2| ≤ (n : ℤ) := by
  have he : |(SMQLPatternRequests.blCharge p).1| = (b : ℤ) := by
    rw [← Int.natCast_natAbs, hb]
  simpa only [he] using charge_degree p

/-- Twice engineering dimension for n fermions and h+d scalar factors. -/
def twiceDimension (n h d : ℕ) : ℕ := 3*n + 2*(h+d)

theorem dimension_lower {n : ℕ} (p : Fin n → Species) (b h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = b) :
    3*((b : ℤ) + |(SMQLPatternRequests.blCharge p).2|) ≤ twiceDimension n h d := by
  have hn := selected_degree p b hb
  unfold twiceDimension
  push_cast
  omega

theorem b1_six_fermions {n : ℕ} (p : Fin n → Species)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = 3)
    (hl : 3 ≤ |(SMQLPatternRequests.blCharge p).2|) : 6 ≤ n := by
  have := selected_degree p 3 hb
  omega

theorem b1_dimension_nine {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = 3)
    (hl : 3 ≤ |(SMQLPatternRequests.blCharge p).2|) : 18 ≤ twiceDimension n h d := by
  have := b1_six_fermions p hb hl
  unfold twiceDimension
  omega

theorem signed_charge_linear {k : ℕ} (q l : ZMod k) (s : Species) :
    DuqlHiggsContent.signedCharge q l s = (baryon s : ZMod k)*q + (lepton s : ZMod k)*l := by
  fin_cases s <;> simp [DuqlHiggsContent.signedCharge, baryon, lepton]

theorem residual_linear {k : ℕ} (q l : ZMod k) {n : ℕ} (p : Fin n → Species) :
    QLFiniteSupport.charge q l p =
      ((SMQLPatternRequests.blCharge p).1 : ZMod k)*q +
      ((SMQLPatternRequests.blCharge p).2 : ZMod k)*l := by
  simp only [QLFiniteSupport.charge, signed_charge_linear, SMQLPatternRequests.blCharge,
    Int.cast_sum, Finset.sum_add_distrib, Finset.sum_mul]

theorem original_even {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) : n % 2 = 0 := by
  obtain ⟨_, m, _, ht⟩ := (SMLowerHiggsSupport.ql_original_iff p q l h d).mp ha
  by_contra hn
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMParityKernelRank.forbidden _ p m.val ((h : ℤ)-d) hn) ht

theorem original_parity {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}
    (p : Fin n → Species) (h d : ℕ)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    ((SMQLPatternRequests.blCharge p).1 + (SMQLPatternRequests.blCharge p).2) % 2 = 0 := by
  have hp := InverseLeptonParitySelection.content_parity p
  have hn : (n : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff n 2).mpr (Nat.dvd_of_mod_eq_zero (original_even q l p h d ha))
  rw [hn] at hp
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hp)

/-- An arithmetic lower bound applies to every actual allowed content,
independently of how a positive witness was selected. -/
theorem original_lepton_lower {k : ℕ} [NeZero k] (q l : ZMod k) (b lower : ℕ)
    (gate : ∀ B L : ℤ, B.natAbs = b → (B+L)%2 = 0 →
      (B : ZMod k)*q + (L : ZMod k)*l = 0 → (lower : ℤ) ≤ |L|)
    {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = b)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    (lower : ℤ) ≤ |(SMQLPatternRequests.blCharge p).2| := by
  apply gate _ _ hb (original_parity q l p h d ha)
  exact (residual_linear q l p).symm.trans ((SMJointHiggsSupport.original_ql_iff p q l h d).mp ha).1

theorem original_degree_lower {k : ℕ} [NeZero k] (q l : ZMod k) (b lower : ℕ)
    (gate : ∀ B L : ℤ, B.natAbs = b → (B+L)%2 = 0 →
      (B : ZMod k)*q + (L : ZMod k)*l = 0 → (lower : ℤ) ≤ |L|)
    {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = b)
    (ha : SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d)) :
    b+lower ≤ n ∧ 3*(b+lower) ≤ twiceDimension n h d := by
  have hl := original_lepton_lower q l b lower gate p h d hb ha
  have hn := selected_degree p b hb
  unfold twiceDimension
  constructor <;> omega

end Physics.SMChargeDegreeBounds
