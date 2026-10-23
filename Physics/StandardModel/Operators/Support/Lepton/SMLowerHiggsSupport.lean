import Physics.StandardModel.Operators.Support.Lepton.SMLowerGenerationSupport
import Physics.StandardModel.Operators.Support.Coordinates.SMParityKernelRank

/-! Complete all-Higgs support for all constant L degrees and Q degrees at most
18, with scalar cyclic q/l residual action retained. -/
namespace Physics.SMLowerHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMLowerGenerationSupport BoundedHiggsSupport
open scoped TensorProduct

variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def localActionEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    ((SMWeylFiniteKernel.fullAction flavor p m delta).comp
      (MonoidHom.inl SMIntegralLocalWeights.Group H))
    (SMIntegralLocalWeights.action flavor p m delta) where
  toLinearEquiv := TensorProduct.congr (.refl ℂ _) (.refl ℂ _)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    rfl

abbrev LocalHiggs (h d : ℕ) :=
  ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m.val ((h : ℤ)-d)))

omit p in
theorem quark_local_iff (n : ℕ) (hn : n=6 ∨ n=12 ∨ n=18) (h d : ℕ) :
    LocalHiggs flavor (pattern 0 n) h d ↔ (n : ℤ)+3*((h : ℤ)-d)=0 := by
  constructor
  · rintro ⟨m,_,ha⟩
    have he := SMChargedKernelRank.local_charge flavor (pattern 0 n) m.val ((h : ℤ)-d) ha
    rwa [quark_charge] at he
  · intro hc
    have hb : n/3 < SMContentWeakBound.bound (pattern 0 n)+1 := by
      rw [quark_bound]; omega
    refine ⟨⟨n/3,hb⟩, ?_, ?_⟩
    · dsimp [Admissible]
      rcases hn with rfl | rfl | rfl <;> omega
    · exact quark_local flavor n (n/3) hn
        (by rcases hn with rfl | rfl | rfl <;> omega) (by omega) ((h : ℤ)-d) hc

omit p in
theorem lepton_local_iff (n : ℕ) (hn : n=2 ∨ n=4 ∨ n=6) (h d : ℕ) :
    LocalHiggs flavor (pattern 3 n) h d ↔ (h : ℤ)-d=n := by
  constructor
  · rintro ⟨m,_,ha⟩
    have he := SMChargedKernelRank.local_charge flavor (pattern 3 n) m.val ((h : ℤ)-d) ha
    rw [lepton_charge] at he
    omega
  · intro hc
    have hb : n < SMContentWeakBound.bound (pattern 3 n)+1 := by rw [lepton_bound]; omega
    refine ⟨⟨n,hb⟩, ?_, ?_⟩
    · dsimp [Admissible]
      rcases hn with rfl | rfl | rfl <;> omega
    · exact lepton_local flavor n n hn
        (by rcases hn with rfl | rfl | rfl <;> omega) (by omega) ((h : ℤ)-d) hc

omit p in
theorem lepton_positive_local_iff (n : ℕ) (hn : 0 < n) (h d : ℕ) :
    LocalHiggs flavor (pattern 3 n) h d ↔ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d=n := by
  constructor
  · rintro ⟨m,hm,ha⟩
    have hc := SMChargedKernelRank.local_charge flavor (pattern 3 n) m.val ((h : ℤ)-d) ha
    rw [lepton_charge] at hc
    have hd : (h : ℤ)-d=n := by omega
    have hp : n % 2=0 := by
      by_contra hp
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMParityKernelRank.forbidden flavor (pattern 3 n) m.val ((h : ℤ)-d) hp) ha
    have hb : m.val ≤ SMConstantWeakCapacity.bound 3 n := by
      by_contra hb
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMConstantWeakCapacity.local_high_forbidden flavor 3 n m.val ((h : ℤ)-d)
          (by omega)) ha
    have hdim : SMConstantWeakCapacity.dimension 3=12 := by
      simpa using SMConstantWeakCapacity.dimension_eq 3
    simp only [SMConstantWeakCapacity.bound, hdim] at hb
    dsimp [Admissible] at hm
    exact ⟨hp, by omega, hd⟩
  · rintro ⟨hp,hmax,hc⟩
    exact (lepton_local_iff flavor n (by omega) h d).mpr hc

omit p in
theorem quark_positive_lower_local_iff (n : ℕ) (hn : 0 < n) (hmax : n ≤ 18) (h d : ℕ) :
    LocalHiggs flavor (pattern 0 n) h d ↔ n % 2=0 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 := by
  constructor
  · rintro ⟨m,_,ha⟩
    have hc := SMChargedKernelRank.local_charge flavor (pattern 0 n) m.val ((h : ℤ)-d) ha
    rw [quark_charge] at hc
    have hp : n % 2=0 := by
      by_contra hp
      exact (SelectionCriteria.forbidden_iff_not_allowed _).mp
        (SMParityKernelRank.forbidden flavor (pattern 0 n) m.val ((h : ℤ)-d) hp) ha
    exact ⟨hp,hc⟩
  · rintro ⟨hp,hc⟩
    exact (quark_local_iff flavor n (by omega) h d).mpr hc

omit p in
theorem vacuum_local_iff (s : DeltaLOneSignedInput.Species) (h d : ℕ) :
    LocalHiggs flavor (pattern s 0) h d ↔ h=d := by
  constructor
  · rintro ⟨m,_,ha⟩
    have he := SMChargedKernelRank.local_charge flavor (pattern s 0) m.val ((h : ℤ)-d) ha
    simp [SMContentWeakBound.hypercharge, pattern, SMConstantWeakCapacity.pattern] at he
    omega
  · intro he
    subst d
    refine ⟨⟨0,by omega⟩, ?_, ?_⟩
    · dsimp [Admissible]; omega
    · have he : (h : ℤ)-h=0 := sub_self _
      rw [he]
      exact vacuum_local flavor s

omit p in
theorem lepton_all_local_iff (n : ℕ) (h d : ℕ) :
    LocalHiggs flavor (pattern 3 n) h d ↔ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d=n := by
  by_cases hn : n=0
  · subst n
    rw [vacuum_local_iff]
    omega
  · exact lepton_positive_local_iff flavor n (by omega) h d

omit p in
theorem quark_lower_local_iff (n : ℕ) (hmax : n ≤ 18) (h d : ℕ) :
    LocalHiggs flavor (pattern 0 n) h d ↔ n % 2=0 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 := by
  by_cases hn : n=0
  · subst n
    rw [vacuum_local_iff]
    omega
  · exact quark_positive_lower_local_iff flavor n (by omega) hmax h d

omit flavor in
def trivialFlavor (s : DeltaLOneSignedInput.Species) :
    Representation ℂ Unit (ThreeGenerationFermionBound.Flavor s) := trivial ℂ Unit _

omit flavor in
theorem local_surjective : Function.Surjective
    (MonoidHom.inl SMIntegralLocalWeights.Group Unit) := by
  rintro ⟨g,u⟩
  exact ⟨g, by cases u; rfl⟩

omit flavor in
def trivialTestEquiv (m : ℕ) (delta : ℤ) : SMFiniteHiggsSupport.Test trivialFlavor p m delta ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action trivialFlavor p m delta) :=
  (InvariantCoefficientTransport.alongSurjection
    (SMWeylFiniteKernel.fullAction trivialFlavor p m delta)
    (MonoidHom.inl SMIntegralLocalWeights.Group Unit) local_surjective).symm.trans
      (InvariantCoefficientTransport.alongEquiv (localActionEquiv trivialFlavor p m delta))

omit flavor in
theorem trivial_original_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace trivialFlavor p h d) ↔
      LocalHiggs trivialFlavor p h d := by
  rw [SMFiniteHiggsSupport.original_allowed_iff]
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => SelectionCriteria.allowed_equiv
    (trivialTestEquiv p m.val ((h : ℤ)-d)))

omit flavor p in
theorem quark_original_iff (n : ℕ) (hn : n=6 ∨ n=12 ∨ n=18) (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace trivialFlavor (pattern 0 n) h d) ↔
      (n : ℤ)+3*((h : ℤ)-d)=0 :=
  (trivial_original_iff (pattern 0 n) h d).trans
    (quark_local_iff trivialFlavor n hn h d)

omit flavor p in
theorem lepton_original_iff (n : ℕ) (hn : n=2 ∨ n=4 ∨ n=6) (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace trivialFlavor (pattern 3 n) h d) ↔
      (h : ℤ)-d=n :=
  (trivial_original_iff (pattern 3 n) h d).trans
    (lepton_local_iff trivialFlavor n hn h d)

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor in
def qlLocalEquiv (m : ℕ) (delta : ℤ) : QLFiniteSupport.LocalTest q l p m delta ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action (QLFiniteSupport.flavor q l) p m delta) :=
  InvariantCoefficientTransport.alongEquiv
    (localActionEquiv (QLFiniteSupport.flavor q l) p m delta)

omit flavor in
theorem ql_original_iff (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
      QLFiniteSupport.charge q l p=0 ∧ LocalHiggs (QLFiniteSupport.flavor q l) p h d := by
  rw [QLFiniteSupport.original_allowed_iff]
  apply and_congr_right
  intro _
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => SelectionCriteria.allowed_equiv
    (qlLocalEquiv p q l m.val ((h : ℤ)-d)))

omit flavor p in
theorem quark_ql_iff (n : ℕ) (hn : n=6 ∨ n=12 ∨ n=18) (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 0 n) h d) ↔
      QLFiniteSupport.charge q l (pattern 0 n)=0 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 :=
  (ql_original_iff (pattern 0 n) q l h d).trans
    (and_congr_right (fun _ => quark_local_iff (QLFiniteSupport.flavor q l) n hn h d))

omit flavor p in
theorem lepton_ql_iff (n : ℕ) (hn : n=2 ∨ n=4 ∨ n=6) (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 3 n) h d) ↔
      QLFiniteSupport.charge q l (pattern 3 n)=0 ∧ (h : ℤ)-d=n :=
  (ql_original_iff (pattern 3 n) q l h d).trans
    (and_congr_right (fun _ => lepton_local_iff (QLFiniteSupport.flavor q l) n hn h d))

omit flavor p [NeZero k] in
theorem quark_residual_charge (n : ℕ) : QLFiniteSupport.charge q l (pattern 0 n) = n • q := by
  simp [QLFiniteSupport.charge, pattern, SMConstantWeakCapacity.pattern,
    DuqlHiggsContent.signedCharge]

omit flavor p [NeZero k] in
theorem lepton_residual_charge (n : ℕ) : QLFiniteSupport.charge q l (pattern 3 n) = n • l := by
  simp [QLFiniteSupport.charge, pattern, SMConstantWeakCapacity.pattern,
    DuqlHiggsContent.signedCharge]

omit flavor p in
theorem lepton_ql_all_iff (n h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 3 n) h d) ↔
      n • l=0 ∧ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d=n := by
  rw [ql_original_iff, lepton_residual_charge, lepton_all_local_iff _ n h d]

omit flavor p in
theorem quark_ql_lower_iff (n : ℕ) (hmax : n ≤ 18) (h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 0 n) h d) ↔
      n • q=0 ∧ n % 2=0 ∧ (n : ℤ)+3*((h : ℤ)-d)=0 := by
  rw [ql_original_iff, quark_residual_charge, quark_lower_local_iff _ n hmax h d]

omit flavor p in
theorem lepton_ql_all_forbidden (n h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 3 n) h d) ↔
      n • l ≠ 0 ∨ n % 2 ≠ 0 ∨ 6 < n ∨ (h : ℤ)-d ≠ n := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, lepton_ql_all_iff q l n h d]
  simp only [not_and_or, not_le]

omit flavor p in
theorem quark_ql_lower_forbidden (n : ℕ) (hmax : n ≤ 18) (h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 0 n) h d) ↔
      n • q ≠ 0 ∨ n % 2 ≠ 0 ∨ (n : ℤ)+3*((h : ℤ)-d) ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, quark_ql_lower_iff q l n hmax h d]
  simp only [not_and_or]

end
end Physics.SMLowerHiggsSupport
