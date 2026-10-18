import Physics.StandardModel.Operators.SMSignedHiggsSupport

/-! Exact permission tests for admissible Q/L Higgs constituents, at all
fermion degrees, with no numerical multiplicity. -/
namespace GUT.SMAdmissibleConstantSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMLowerGenerationSupport SMLowerHiggsSupport
open BoundedHiggsSupport

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

theorem weak_le (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ)
    (ha : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern s n) m delta))) :
    m ≤ SMConstantWeakCapacity.bound s n := by
  by_contra hb
  exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
    (SMConstantWeakCapacity.local_high_forbidden flavor s n m delta (by omega)) ha

theorem quark_local_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 0 n) m ((h : ℤ)-d))) ↔
    n % 2=0 ∧ n ≤ 24 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 ∧ m ≤ min n (36-n) := by
  constructor
  · intro ha
    have hdim : SMConstantWeakCapacity.dimension 0=36 := by
      simpa using SMConstantWeakCapacity.dimension_eq 0
    have hb : m ≤ min n (36-n) := by
      simpa only [SMConstantWeakCapacity.bound, hdim] using weak_le flavor 0 n m ((h : ℤ)-d) ha
    have ht := (SMQuarkAllHiggsSupport.local_higgs_iff flavor n h d).mp
      ⟨⟨m,by rw [quark_bound]; omega⟩,had,ha⟩
    exact ⟨ht.1,ht.2.1,ht.2.2,hb⟩
  · rintro ⟨hp,hn,hc,hb⟩
    have hm : m % 2=0 := by dsimp [Admissible] at had; omega
    by_cases hz : n=0
    · subst n
      have hm0 : m=0 := by omega
      subst m
      have he : (h : ℤ)-d=0 := by omega
      rw [he]
      exact vacuum_local flavor 0
    · by_cases hlo : n ≤ 18
      · exact SMLowerGenerationSupport.quark_local flavor n m (by omega) hm (by omega) ((h : ℤ)-d) hc
      · have hn24 : n=24 := by omega
        subst n
        exact SMQuarkAllHiggsSupport.twenty_four_local flavor m hm (by omega) ((h : ℤ)-d) hc

theorem lepton_local_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 3 n) m ((h : ℤ)-d))) ↔
    n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d=n ∧ m=n := by
  constructor
  · intro ha
    have hb := weak_le flavor 3 n m ((h : ℤ)-d) ha
    have hmn : m ≤ n := hb.trans (Nat.min_le_left _ _)
    have ht := (lepton_all_local_iff flavor n h d).mp
      ⟨⟨m,by rw [lepton_bound]; omega⟩,had,ha⟩
    dsimp [Admissible] at had
    exact ⟨ht.1,ht.2.1,ht.2.2,by omega⟩
  · rintro ⟨hp,hn,hc,hm⟩
    subst m
    by_cases hz : n=0
    · subst n
      rw [hc]
      exact vacuum_local flavor 3
    · exact SMLowerGenerationSupport.lepton_local flavor n n (by omega) hp le_rfl ((h : ℤ)-d) hc

theorem conjugate_quark_local_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 5 n) m ((h : ℤ)-d))) ↔
    n % 2=0 ∧ n ≤ 24 ∧ -(n : ℤ)+3*((h : ℤ)-d)=0 ∧ m ≤ min n (36-n) := by
  rw [SelectionCriteria.allowed_equiv (SMSignedHiggsSupport.coefficientEquiv flavor 5 n m ((h : ℤ)-d))]
  have he : -((h : ℤ)-d)=(d : ℤ)-h := by ring
  change SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor (pattern 0 n) m (-((h : ℤ)-d)))) ↔ _
  rw [he, quark_local_iff flavor n d h m (by dsimp [Admissible] at had ⊢; omega)]
  omega

theorem conjugate_lepton_local_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern 8 n) m ((h : ℤ)-d))) ↔
    n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d= -(n : ℤ) ∧ m=n := by
  rw [SelectionCriteria.allowed_equiv (SMSignedHiggsSupport.coefficientEquiv flavor 8 n m ((h : ℤ)-d))]
  have he : -((h : ℤ)-d)=(d : ℤ)-h := by ring
  change SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    (SMIntegralLocalWeights.action flavor (pattern 3 n) m (-((h : ℤ)-d)))) ↔ _
  rw [he, lepton_local_iff flavor n d h m (by dsimp [Admissible] at had ⊢; omega)]
  omega

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
theorem ql_test_iff {r : ℕ} (p : Fin r → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l p m delta) ↔ QLFiniteSupport.charge q l p=0 ∧
      SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
        (SMIntegralLocalWeights.action (QLFiniteSupport.flavor q l) p m delta)) :=
  (QLFiniteSupport.test_allowed_iff q l p m delta).trans
    (and_congr_right (fun _ => SelectionCriteria.allowed_equiv (qlLocalEquiv p q l m delta)))

omit flavor in
theorem quark_ql_test_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l (pattern 0 n) m ((h : ℤ)-d)) ↔
    n • q=0 ∧ n % 2=0 ∧ n ≤ 24 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 ∧ m ≤ min n (36-n) := by
  rw [ql_test_iff, quark_residual_charge, quark_local_iff _ n h d m had]

omit flavor in
theorem lepton_ql_test_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l (pattern 3 n) m ((h : ℤ)-d)) ↔
    n • l=0 ∧ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d=n ∧ m=n := by
  rw [ql_test_iff, lepton_residual_charge, lepton_local_iff _ n h d m had]

omit flavor in
theorem conjugate_quark_ql_test_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l (pattern 5 n) m ((h : ℤ)-d)) ↔
    n • q=0 ∧ n % 2=0 ∧ n ≤ 24 ∧ -(n : ℤ)+3*((h : ℤ)-d)=0 ∧ m ≤ min n (36-n) := by
  rw [ql_test_iff, SMSignedHiggsSupport.conjugate_quark_charge, neg_eq_zero,
    conjugate_quark_local_iff _ n h d m had]

omit flavor in
theorem conjugate_lepton_ql_test_iff (n h d m : ℕ) (had : Admissible h d m) :
    SelectionCriteria.Allowed (QLFiniteSupport.Test q l (pattern 8 n) m ((h : ℤ)-d)) ↔
    n • l=0 ∧ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d= -(n : ℤ) ∧ m=n := by
  rw [ql_test_iff, SMSignedHiggsSupport.conjugate_lepton_charge, neg_eq_zero,
    conjugate_lepton_local_iff _ n h d m had]

end
end GUT.SMAdmissibleConstantSupport
