import Math.RepresentationTheory.GradedSymmetryProtection
import Math.RepresentationTheory.MixedChargeSelection

/-! Stable content specifications compose without changing field actions. -/
namespace Math.ProhibitionSpecification
set_option autoImplicit false
noncomputable section
variable {P Q : Type*}

structure Spec (P Q : Type*) where
  test : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop
  stable : ∀ n m p s (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
    test n m (p ∘ e) (s ∘ f) ↔ test n m p s

def pullback {A : Type*} (v : ∀ n m, (Fin n → P) → (Fin m → Q) → A)
    (h : ∀ n m p s (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
      v n m (p ∘ e) (s ∘ f) = v n m p s) (t : A → Prop) : Spec P Q :=
  ⟨fun n m p s => t (v n m p s), by intros; rw [h]⟩
def empty : Spec P Q := ⟨fun _ _ _ _ => False, by intros; rfl⟩
def full : Spec P Q := ⟨fun _ _ _ _ => True, by intros; rfl⟩
def union (s t : Spec P Q) : Spec P Q :=
  ⟨fun n m p q => s.test n m p q ∨ t.test n m p q,
    by intros; rw [s.stable, t.stable]⟩
def inter (s t : Spec P Q) : Spec P Q :=
  ⟨fun n m p q => s.test n m p q ∧ t.test n m p q,
    by intros; rw [s.stable, t.stable]⟩
def compl (s : Spec P Q) : Spec P Q :=
  ⟨fun n m p q => ¬ s.test n m p q, by intros; rw [s.stable]⟩
def iUnion {I : Type*} (s : I → Spec P Q) : Spec P Q :=
  ⟨fun n m p q => ∃ i, (s i).test n m p q,
    by intros; simp only [(s _).stable]⟩
def charges {A : Type*} [AddCommGroup A] (fq : P → A) (bq : Q → A)
    (t : A → Prop) : Spec P Q :=
  pullback (fun _ _ => MixedChargeSelection.charge fq bq)
    (fun _ _ => MixedChargeSelection.charge_stable fq bq) t

section Content
/-- A contentwise property; instantiated below with vanishing or restriction surjectivity. -/
def Satisfies (s : Spec P Q) (n m : ℕ)
    (r : MixedContentOrbits.Content (P := P) (Q := Q) (n := n) (m := m) → Prop) :=
  ∀ x, s.test n m x.out.1 x.out.2 → r x

theorem union_iff (s t : Spec P Q) (n m : ℕ) (r) :
    Satisfies (union s t) n m r ↔ Satisfies s n m r ∧ Satisfies t n m r := by
  simp only [Satisfies, union, or_imp, forall_and]
theorem iUnion_iff {I : Type*} (s : I → Spec P Q) (n m : ℕ) (r) :
    Satisfies (iUnion s) n m r ↔ ∀ i, Satisfies (s i) n m r := by
  constructor
  · intro h i x hx; exact h x ⟨i,hx⟩
  · rintro h x ⟨i,hx⟩; exact h i x hx
theorem mono (s t : Spec P Q) (n m : ℕ) (r)
    (h : ∀ p q, s.test n m p q → t.test n m p q)
    (ht : Satisfies t n m r) : Satisfies s n m r :=
  fun x hx => ht x (h _ _ hx)
theorem inter_of_left (s t : Spec P Q) (n m : ℕ) (r)
    (hs : Satisfies s n m r) : Satisfies (inter s t) n m r :=
  fun x hx => hs x hx.1
theorem empty_satisfies (n m : ℕ) (r) : Satisfies (empty : Spec P Q) n m r :=
  fun _ h => False.elim h
theorem all_union_iff (s t : Spec P Q)
    (r : ∀ n m, MixedContentOrbits.Content (P := P) (Q := Q) (n := n) (m := m) → Prop) :
    (∀ n m, Satisfies (union s t) n m (r n m)) ↔
      (∀ n m, Satisfies s n m (r n m)) ∧ (∀ n m, Satisfies t n m (r n m)) := by
  simp only [union_iff, forall_and]
end Content
end
end Math.ProhibitionSpecification
