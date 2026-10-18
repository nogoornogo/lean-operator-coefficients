import Math.RepresentationTheory.ProhibitionSpecification
namespace Math.ComposableProtection
set_option autoImplicit false
noncomputable section
open Representation
open ProhibitionSpecification
variable {P Q G H J : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H] [Group J]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))


theorem forbidden_iff (s : Spec P Q) (n m : ℕ) :
    (∀ f : MixedSpeciesProjection.supportSpace (s.test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ↔
    Satisfies s n m (fun x => ∀ q : GradedMixedCompleteness.Factor a b c d n m x, q = 0) := by
  classical
  rw [GradedMixedCompleteness.selected_forbidden_iff a b c d n m _ (s.stable n m)]
  constructor
  · intro h x hx; exact h ⟨x,hx⟩
  · intro h x; exact h x.val x.property

theorem protected_iff (j : J →* H) (s : Spec P Q) (n m : ℕ) :
    GradedSymmetryProtection.Protected a b c d j s.test n m ↔
    Satisfies s n m (fun x => Function.Surjective
      (GradedCompletenessRestriction.factorMap a b c d j n m x)) := by
  classical
  rw [GradedSymmetryProtection.protected_iff_factors a b c d j s.test s.stable n m]
  constructor
  · intro h x hx; exact h ⟨x,hx⟩
  · intro h x; exact h x.val x.property

theorem forbidden_union_iff (s t : Spec P Q) (n m : ℕ) :
    (∀ f : MixedSpeciesProjection.supportSpace ((union s t).test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ↔
    (∀ f : MixedSpeciesProjection.supportSpace (s.test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ∧
    (∀ f : MixedSpeciesProjection.supportSpace (t.test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) := by
  rw [forbidden_iff, forbidden_iff, forbidden_iff, union_iff]

theorem protected_union_iff (j : J →* H) (s t : Spec P Q) (n m : ℕ) :
    GradedSymmetryProtection.Protected a b c d j (union s t).test n m ↔
      GradedSymmetryProtection.Protected a b c d j s.test n m ∧
      GradedSymmetryProtection.Protected a b c d j t.test n m := by
  rw [protected_iff, protected_iff, protected_iff, union_iff]

theorem all_forbidden_union_iff (s t : Spec P Q) :
    (∀ n m, ∀ f : MixedSpeciesProjection.supportSpace ((union s t).test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ↔
    (∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (s.test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ∧
    (∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (t.test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) := by
  simp only [forbidden_union_iff, forall_and]

theorem all_protected_union_iff (j : J →* H) (s t : Spec P Q) :
    (∀ n m, GradedSymmetryProtection.Protected a b c d j (union s t).test n m) ↔
    (∀ n m, GradedSymmetryProtection.Protected a b c d j s.test n m) ∧
    (∀ n m, GradedSymmetryProtection.Protected a b c d j t.test n m) := by
  simp only [protected_union_iff, forall_and]

theorem charges_forbidden {A : Type*} [AddCommGroup A]
    (fq : P → A) (bq : Q → A) (chi : H → AddChar A ℂ)
    (hf : ∀ g u v, c u g v = chi g (fq u) • v)
    (hb : ∀ g u v, d u g v = chi g (bq u) • v)
    (t : A → Prop)
    (detect : ∀ n m (p : Fin n → P) (q : Fin m → Q),
      t (MixedChargeSelection.charge fq bq p q) →
      ∃ g, chi g (MixedChargeSelection.charge fq bq p q) ≠ 1) :
    ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace ((charges fq bq t).test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0 := by
  classical
  exact MixedChargeSelection.all_forbidden a b c d fq bq chi hf hb
    (charges fq bq t).test (charges fq bq t).stable detect
end
end Math.ComposableProtection
