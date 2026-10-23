import Math.RepresentationTheory.Protection.ProhibitionPatterns

namespace Math.AdmittedCyclicProhibition
set_option autoImplicit false
noncomputable section
open Representation ProhibitionSpecification SelectionCriteria
variable {k : ℕ} [NeZero k]
variable {P Q G : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ (CyclicCharge.Group k) (M u)) (d : ∀ u, Representation ℂ (CyclicCharge.Group k) (N u))

  (fq : P → ZMod k) (bq : Q → ZMod k)
  (hf : ∀ g u v, c u g v = MixedChargeSelection.cyclicCharacter g (fq u) • v)
  (hb : ∀ g u v, d u g v = MixedChargeSelection.cyclicCharacter g (bq u) • v)

include hf hb in
/-- The support guard refers to the actual carrier after local/statistics quotients. -/
theorem forbidden_iff (s : Spec P Q) (n m : ℕ) :
    ProhibitionInput.Forbids a b c d s n m ↔
    ∀ x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m,
      s.test n m x.out.1 x.out.2 →
      Nontrivial (TypedMixedSeparatedHom.Carrier a b c d x.out.1 x.out.2) →
      MixedChargeSelection.charge fq bq x.out.1 x.out.2 ≠ 0 := by
  constructor
  · intro h x hx hn
    have := hn
    exact (MixedChargeSelection.cyclic_detect_iff _).mp
      (ProhibitionInput.charge_detected a b c d fq bq
        MixedChargeSelection.cyclicCharacter hf hb s n m h x hx)
  · intro h
    apply (ProhibitionInput.factors_iff a b c d s n m).mpr
    intro x hx
    let r := TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2
    by_cases hn : Nontrivial (TypedMixedSeparatedHom.Carrier a b c d x.out.1 x.out.2)
    · have := hn
      apply (ProhibitionPatterns.cyclic_forbidden_iff r _ ?_).mpr (h x hx hn)
      intro g v
      rw [← MixedChargeSelection.total_eq_character]
      exact MixedScalarSelection.residual_scalar a b c d x.out.1 x.out.2 g
        (fun u => MixedChargeSelection.cyclicCharacter g (fq u))
        (fun u => MixedChargeSelection.cyclicCharacter g (bq u)) (hf g) (hb g) v
    · have : Subsingleton (TypedMixedSeparatedHom.Carrier a b c d x.out.1 x.out.2) :=
        not_nontrivial_iff_subsingleton.mp hn
      exact ScalarProhibitionNecessity.zero_carrier_forbidden r

include hf hb in
theorem all_forbidden_iff (s : Spec P Q) :
    ProhibitionInput.AllForbids a b c d s ↔
    ∀ n m, ∀ x : GradedMixedCompleteness.Content (P := P) (Q := Q) n m,
      s.test n m x.out.1 x.out.2 →
      Nontrivial (TypedMixedSeparatedHom.Carrier a b c d x.out.1 x.out.2) →
      MixedChargeSelection.charge fq bq x.out.1 x.out.2 ≠ 0 := by
  unfold ProhibitionInput.AllForbids
  simp only [forbidden_iff a b c d fq bq hf hb]
end
end Math.AdmittedCyclicProhibition
