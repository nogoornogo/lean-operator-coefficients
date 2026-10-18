import Physics.StandardModel.Operators.SMMixedLeptonDictionary
import Physics.StandardModel.Operators.SMLeptonMaximalLocal
import Physics.StandardModel.Operators.SMLocalCoefficientGluing

/-! Full all-Higgs support for signed L/conjugate-L mixtures.
The proof constructs nonzero coupled coefficients, without evaluating rank
or multiplicity. Both independent chirality centers remain enforced. -/
namespace GUT.SMMixedLeptonSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMMixedLeptonDictionary

abbrev distance (a b : ℕ) := if a≤b then b-a else a-b

theorem maximal_triangle (a b : ℕ) (ha : a≤12) (hb : b≤12)
    (hea : a%2=0) (heb : b%2=0)
    (hl : -((capacity a+capacity b : ℕ) : ℤ)≤(a : ℤ)-b)
    (hu : (a : ℤ)-b≤((capacity a+capacity b : ℕ) : ℤ)) :
    SU2PairCoupling.Triangle (capacity a) (capacity b) (distance a b) := by
  dsimp [capacity] at hl hu
  unfold SU2PairCoupling.Triangle capacity distance
  split_ifs <;> omega

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

theorem local_iff (a b h d : ℕ) :
    SMLowerHiggsSupport.LocalHiggs flavor (pattern a b) h d ↔
      a≤12 ∧ b≤12 ∧ a%2=0 ∧ b%2=0 ∧ (h : ℤ)-d=(a : ℤ)-b ∧
      -((capacity a+capacity b : ℕ) : ℤ)≤(a : ℤ)-b ∧
      (a : ℤ)-b≤((capacity a+capacity b : ℕ) : ℤ) := by
  constructor
  · rintro ⟨m,had,ht⟩
    have hc : SMContentCapacity.Fits (pattern a b) := by
      by_contra hn
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMContentCapacity.local_forbidden flavor (pattern a b) hn m.val ((h : ℤ)-d)) ht
    obtain ⟨ha,hb⟩ := (fits a b).mp hc
    have parity (side : Bool) : SMChiralitySupport.count (pattern a b) side%2=0 := by
      by_contra hn
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMChiralitySupport.local_forbidden flavor (pattern a b) side hn m.val ((h : ℤ)-d)) ht
    have hpa : a%2=0 := by simpa [chirality] using parity false
    have hpb : b%2=0 := by simpa [chirality] using parity true
    have hcharge := SMChargedKernelRank.local_charge flavor (pattern a b) m.val ((h : ℤ)-d) ht
    rw [hypercharge] at hcharge
    have hd : (h : ℤ)-d=(a : ℤ)-b := by omega
    have hm : m.val≤capacity a+capacity b := by
      by_contra hn
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMMixedWeakCapacity.local_high_forbidden flavor (pattern a b) m.val ((h : ℤ)-d)
          (by rw [sharp_bound]; omega)) ht
    dsimp [BoundedHiggsSupport.Admissible] at had
    exact ⟨ha,hb,hpa,hpb,hd,by omega,by omega⟩
  · rintro ⟨ha,hb,hpa,hpb,hd,hl,hu⟩
    obtain ⟨r,hr⟩ := (SU2PairCoupling.degree_exists_iff (capacity a) (capacity b) (distance a b)).mpr
      (maximal_triangle a b ha hb hpa hpb hl hu)
    have hm : distance a b<SMContentWeakBound.bound (pattern a b)+1 := by
      rw [raw_bound]
      dsimp [distance]
      split_ifs <;> omega
    refine ⟨⟨distance a b,hm⟩,?_,?_⟩
    · dsimp [BoundedHiggsSupport.Admissible,distance]
      split_ifs <;> omega
    · have he : (a : ℤ)+(-(b : ℤ))=(h : ℤ)-d := by omega
      exact SMLocalCoefficientGluing.allowed_at flavor 3 8 a b (capacity a) (capacity b)
        (by decide) r (a : ℤ) (-(b : ℤ)) (distance a b) ((h : ℤ)-d) hr he
        (SMLeptonMaximalLocal.positive flavor a ha hpa)
        (SMLeptonMaximalLocal.negative flavor b hb hpb)


variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
theorem original_ql_iff (a b h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (QLFiniteSupport.flavor q l) (pattern a b) h d) ↔
      a • l-b • l=0 ∧ a≤12 ∧ b≤12 ∧ a%2=0 ∧ b%2=0 ∧
      (h : ℤ)-d=(a : ℤ)-b ∧
      -((capacity a+capacity b : ℕ) : ℤ)≤(a : ℤ)-b ∧
      (a : ℤ)-b≤((capacity a+capacity b : ℕ) : ℤ) := by
  rw [SMLowerHiggsSupport.ql_original_iff,SMMixedLeptonDictionary.residual,local_iff]

end
end GUT.SMMixedLeptonSupport
