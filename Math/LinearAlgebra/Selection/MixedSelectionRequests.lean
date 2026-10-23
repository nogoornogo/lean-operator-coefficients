import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Per-target zero/nonzero requests; allowed targets may use different witnesses. -/
namespace Math.MixedSelectionRequests
set_option autoImplicit false
open SelectionCriteria

structure Request (I : Type*) where
  forbid : Set I
  allow : Set I

variable {I : Type*} (C : I → Type*) [∀ i, Zero (C i)]

def Satisfies (r : Request I) : Prop :=
  (∀ i ∈ r.forbid, Forbidden (C i)) ∧ (∀ i ∈ r.allow, Allowed (C i))

def combine (r s : Request I) : Request I :=
  ⟨r.forbid ∪ s.forbid, r.allow ∪ s.allow⟩

theorem forbidden (r : Request I) (h : Satisfies C r) (i : I) (hi : i ∈ r.forbid) :
    Forbidden (C i) := h.1 i hi

theorem allowed (r : Request I) (h : Satisfies C r) (i : I) (hi : i ∈ r.allow) :
    Allowed (C i) := h.2 i hi

theorem combine_iff (r s : Request I) :
    Satisfies C (combine r s) ↔ Satisfies C r ∧ Satisfies C s := by
  constructor
  · intro h
    exact ⟨⟨fun i hi => h.1 i (Or.inl hi), fun i hi => h.2 i (Or.inl hi)⟩,
      ⟨fun i hi => h.1 i (Or.inr hi), fun i hi => h.2 i (Or.inr hi)⟩⟩
  · rintro ⟨hr,hs⟩
    constructor
    · intro i hi; rcases hi with hi | hi
      · exact hr.1 i hi
      · exact hs.1 i hi
    · intro i hi; rcases hi with hi | hi
      · exact hr.2 i hi
      · exact hs.2 i hi

theorem conflict (r : Request I) (i : I) (hf : i ∈ r.forbid) (ha : i ∈ r.allow) :
    ¬ Satisfies C r := by
  intro h
  exact (forbidden_iff_not_allowed (C i)).mp (h.1 i hf) (h.2 i ha)

theorem empty_satisfied : Satisfies C ⟨∅, ∅⟩ := by
  constructor <;> intro i hi <;> cases hi

section Linear
variable {k : Type*} [Field k]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def SelectedAllowed (s : V →ₗ[k] W) : Prop := ∃ v, s v ≠ 0

theorem selected_allowed_iff_range (s : V →ₗ[k] W) :
    SelectedAllowed s ↔ Allowed s.range := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨⟨s v, ⟨v,rfl⟩⟩, fun h => hv (congrArg Subtype.val h)⟩
  · rintro ⟨⟨w,v,rfl⟩,hw⟩
    exact ⟨v, fun h => hw (Subtype.ext h)⟩

theorem selector_zero_iff_not_allowed (s : V →ₗ[k] W) :
    s = 0 ↔ ¬ SelectedAllowed s := by
  simp only [SelectedAllowed, not_exists, not_not]
  exact ⟨fun h v => by simp [h], fun h => LinearMap.ext h⟩

theorem range_forbidden_iff (s : V →ₗ[k] W) : Forbidden s.range ↔ s = 0 := by
  rw [forbidden_iff_not_allowed, ← selected_allowed_iff_range, selector_zero_iff_not_allowed]
/-- A nonzero whole domain can have an identically zero prescribed selector. -/
theorem whole_domain_not_selected : Allowed k ∧ ¬ SelectedAllowed (0 : k →ₗ[k] k) :=
  ⟨⟨1, one_ne_zero⟩, (selector_zero_iff_not_allowed _).mp rfl⟩
end Linear

section Transport
variable {k : Type*} [Semiring k] {D E : I → Type*}
  [∀ i, AddCommMonoid (D i)] [∀ i, Module k (D i)]
  [∀ i, AddCommMonoid (E i)] [∀ i, Module k (E i)]

theorem transport (r : Request I) (e : ∀ i, D i ≃ₗ[k] E i) :
    Satisfies D r ↔ Satisfies E r := by
  constructor
  · intro h
    exact ⟨fun i hi => (ofEquiv (e i)).forbidden.mp (h.1 i hi),
      fun i hi => (allowed_equiv (e i)).mp (h.2 i hi)⟩
  · intro h
    exact ⟨fun i hi => (ofEquiv (e i)).forbidden.mpr (h.1 i hi),
      fun i hi => (allowed_equiv (e i)).mpr (h.2 i hi)⟩
end Transport
end Math.MixedSelectionRequests
