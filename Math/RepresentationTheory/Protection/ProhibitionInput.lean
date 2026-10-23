import Math.RepresentationTheory.Protection.ComposableProtection
import Math.RepresentationTheory.Decomposition.CommonIrreducible
import Math.RepresentationTheory.Protection.ScalarProhibitionNecessity

namespace Math.ProhibitionInput
set_option autoImplicit false
noncomputable section
open Representation ProhibitionSpecification SelectionCriteria
variable {P Q G H J : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H] [Group J]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))


abbrev Forbids (s : Spec P Q) (n m : ℕ) : Prop :=
  Forbidden (MixedSpeciesProjection.supportSpace (s.test n m)
    (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d))
abbrev AllForbids (s : Spec P Q) : Prop := ∀ n m, Forbids a b c d s n m

theorem factors_iff (s : Spec P Q) (n m : ℕ) :
    Forbids a b c d s n m ↔ Satisfies s n m
      (fun x => Forbidden (GradedMixedCompleteness.Factor a b c d n m x)) :=
  ComposableProtection.forbidden_iff a b c d s n m

theorem factor (s : Spec P Q) (n m : ℕ) (h : Forbids a b c d s n m)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m)
    (hx : s.test n m x.out.1 x.out.2) :
    Forbidden (GradedMixedCompleteness.Factor a b c d n m x) :=
  (factors_iff a b c d s n m).mp h x hx

theorem mono (s t : Spec P Q) (n m : ℕ)
    (hst : ∀ p q, s.test n m p q → t.test n m p q)
    (ht : Forbids a b c d t n m) : Forbids a b c d s n m :=
  (factors_iff a b c d s n m).mpr
    (ProhibitionSpecification.mono s t n m _ hst ((factors_iff a b c d t n m).mp ht))

theorem all_mono (s t : Spec P Q)
    (hst : ∀ n m p q, s.test n m p q → t.test n m p q)
    (ht : AllForbids a b c d t) : AllForbids a b c d s :=
  fun n m => mono a b c d s t n m (hst n m) (ht n m)

theorem union_iff (s t : Spec P Q) (n m : ℕ) :
    Forbids a b c d (union s t) n m ↔
      Forbids a b c d s n m ∧ Forbids a b c d t n m :=
  ComposableProtection.forbidden_union_iff a b c d s t n m

theorem iUnion_iff {I : Type*} (s : I → Spec P Q) (n m : ℕ) :
    Forbids a b c d (iUnion s) n m ↔ ∀ i, Forbids a b c d (s i) n m := by
  simp only [factors_iff, ProhibitionSpecification.iUnion_iff]

theorem all_union_iff (s t : Spec P Q) :
    AllForbids a b c d (union s t) ↔ AllForbids a b c d s ∧ AllForbids a b c d t := by
  simp only [AllForbids, union_iff, forall_and]

theorem all_iUnion_iff {I : Type*} (s : I → Spec P Q) :
    AllForbids a b c d (iUnion s) ↔ ∀ i, AllForbids a b c d (s i) := by
  simp only [AllForbids, iUnion_iff]
  constructor
  · intro h i n m; exact h n m i
  · intro h n m i; exact h i n m

theorem empty_forbids (n m : ℕ) : Forbids a b c d empty n m :=
  (factors_iff a b c d empty n m).mpr (empty_satisfies n m _)

theorem no_shared (s : Spec P Q) (n m : ℕ) (h : Forbids a b c d s n m)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m)
    (hx : s.test n m x.out.1 x.out.2)
    (hr : IsSemisimpleRepresentation
      (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2)) :
    ¬ CommonIrreducible.Shares
      (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2) (trivial ℂ H ℂ) :=
  (CommonIrreducible.all_zero_iff _ _ hr).mp (factor a b c d s n m h x hx)

theorem no_shared_iff (s : Spec P Q) (n m : ℕ)
    (hr : ∀ x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m,
      s.test n m x.out.1 x.out.2 → IsSemisimpleRepresentation
        (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2)) :
    Forbids a b c d s n m ↔ Satisfies s n m (fun x => ¬ CommonIrreducible.Shares
      (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2) (trivial ℂ H ℂ)) := by
  constructor
  · intro h x hx; exact no_shared a b c d s n m h x hx (hr x hx)
  · intro h
    apply (factors_iff a b c d s n m).mpr
    intro x hx
    exact (CommonIrreducible.all_zero_iff _ _ (hr x hx)).mpr (h x hx)

theorem shared_defeats (s : Spec P Q) (n m : ℕ)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m)
    (hx : s.test n m x.out.1 x.out.2)
    (hr : IsSemisimpleRepresentation
      (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2))
    (hs : CommonIrreducible.Shares
      (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2) (trivial ℂ H ℂ)) :
    ¬ Forbids a b c d s n m := fun h => no_shared a b c d s n m h x hx hr hs

/-- Equivalence transport reuses the existing selection certificate. -/
theorem transport {C : Type*} [AddCommGroup C] [Module ℂ C]
    (s : Spec P Q) (n m : ℕ)
    (e : MixedSpeciesProjection.supportSpace (s.test n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d) ≃ₗ[ℂ] C) :
    Forbids a b c d s n m ↔ Forbidden C := (SelectionCriteria.ofEquiv e).forbidden

/-- Necessity is on the admitted local/statistics quotient, not the raw tensor. -/
theorem charge_detected {A : Type*} [AddCommGroup A]
    (fq : P → A) (bq : Q → A) (chi : H → AddChar A ℂ)
    (hf : ∀ g u v, c u g v = chi g (fq u) • v)
    (hb : ∀ g u v, d u g v = chi g (bq u) • v)
    (s : Spec P Q) (n m : ℕ) (h : Forbids a b c d s n m)
    (x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m)
    (hx : s.test n m x.out.1 x.out.2)
    [Nontrivial (TypedMixedSeparatedHom.Carrier a b c d x.out.1 x.out.2)] :
    ∃ g, chi g (MixedChargeSelection.charge fq bq x.out.1 x.out.2) ≠ 1 := by
  apply (ScalarProhibitionNecessity.forbidden_iff_detect
    (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2)
    (fun g => chi g (MixedChargeSelection.charge fq bq x.out.1 x.out.2)) ?_).mp
    (factor a b c d s n m h x hx)
  intro g v
  rw [← MixedChargeSelection.total_eq_character]
  exact MixedScalarSelection.residual_scalar a b c d x.out.1 x.out.2 g
    (fun u => chi g (fq u)) (fun u => chi g (bq u)) (hf g) (hb g) v

theorem restriction_obstruction (j : J →* H) (s : Spec P Q) (n m : ℕ)
    (h : Forbids a b c d s n m)
    (ha : Allowed (MixedSpeciesProjection.supportSpace (s.test n m)
      (TypedMixedSeparatedHom.fieldF a (fun u => (c u).comp j))
      (TypedMixedSeparatedHom.fieldB b (fun u => (d u).comp j)))) :
    ¬ Function.Surjective (GradedCompletenessRestriction.selectedMap a b c d j n m
      (s.test n m)) := by
  classical
  exact ScalarProhibitionNecessity.not_surjective _ (map_zero _) h ha
end
end Math.ProhibitionInput
