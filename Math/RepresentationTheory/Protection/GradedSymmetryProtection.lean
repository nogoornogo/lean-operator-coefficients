import Math.RepresentationTheory.Coefficients.GradedCompletenessAllRestriction
import Math.RepresentationTheory.Protection.InvariantProtection

/-! All-degree symmetry enhancement on independent mixed-statistics inputs. -/
namespace Math.GradedSymmetryProtection
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q G H J : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H] [Group J]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (j : J →* H)
  (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)
  [∀ n m v w, Decidable (allowed n m v w)]
  (stable : ∀ n m v w (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
    allowed n m (v ∘ p) (w ∘ q) ↔ allowed n m v w)


/-- Every smaller-group coefficient obeys the larger physical action. -/
def Protected (n m : ℕ) : Prop :=
  ∀ f : MixedSpeciesProjection.supportSpace (allowed n m)
    (TypedMixedSeparatedHom.fieldF a (fun u => (c u).comp j))
    (TypedMixedSeparatedHom.fieldB b (fun u => (d u).comp j)),
  ∀ gh v, f.val (((FiniteSpeciesExterior.representation (TypedMixedSeparatedHom.fieldF a c)).exteriorPower n).tprod
    ((FiniteSpeciesExterior.representation (TypedMixedSeparatedHom.fieldB b d)).symmetricPower m) gh v) = f.val v

omit [∀ n m v w, Decidable (allowed n m v w)] in
theorem protected_iff_surjective (n m : ℕ) : Protected a b c d j allowed n m ↔
    Function.Surjective (GradedCompletenessRestriction.selectedMap a b c d j n m (allowed n m)) := by
  constructor
  · intro hp f
    let q : MixedSpeciesProjection.supportSpace (allowed n m)
        (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d) :=
      ⟨{
        toLinearMap := f.val.toLinearMap
        isIntertwining' gh := by
          apply LinearMap.ext
          intro v
          exact hp f gh v }, f.property⟩
    exact ⟨q, Subtype.ext (IntertwiningMap.ext rfl)⟩
  · intro hs f gh v
    obtain ⟨q, rfl⟩ := hs f
    exact IntertwiningMap.isIntertwining _ _ q.val gh v

include stable in
theorem protected_iff_residual_surjective (n m : ℕ) : Protected a b c d j allowed n m ↔
    Function.Surjective (GradedCompletenessRestriction.selectedProductMap a b c d j n m (allowed n m)) :=
  (protected_iff_surjective a b c d j allowed n m).trans
    (InvariantProtection.square_surjective_iff
      (GradedMixedCompleteness.selectedEquiv a b c d n m (allowed n m) (stable n m))
      (GradedMixedCompleteness.selectedEquiv a b (fun u => (c u).comp j)
        (fun u => (d u).comp j) n m (allowed n m) (stable n m))
      _ _ (GradedCompletenessRestriction.selected_extraction a b c d j n m
        (allowed n m) (stable n m)))

omit [∀ n m v w, Decidable (allowed n m v w)] in
theorem all_protected_iff_input_surjective :
    (∀ n m, Protected a b c d j allowed n m) ↔
    Function.Surjective (GradedCompletenessAllRestriction.inputMap a b c d j allowed) := by
  have h := InvariantProtection.family_surjective_iff
    (fun z : ℕ × ℕ => GradedCompletenessRestriction.selectedMap a b c d j z.1 z.2 (allowed z.1 z.2))
  change (∀ n m, Protected a b c d j allowed n m) ↔ Function.Surjective
    (InvariantProtection.familyMap (fun z : ℕ × ℕ =>
      GradedCompletenessRestriction.selectedMap a b c d j z.1 z.2 (allowed z.1 z.2)))
  rw [h]
  constructor
  · intro hp z
    exact (protected_iff_surjective a b c d j allowed z.1 z.2).mp (hp z.1 z.2)
  · intro hs n m
    exact (protected_iff_surjective a b c d j allowed n m).mpr (hs (n,m))

include stable in
theorem all_protected_iff_hom_surjective :
    (∀ n m, Protected a b c d j allowed n m) ↔
    Function.Surjective (GradedCompletenessAllRestriction.homMap a b c d j allowed) :=
  (all_protected_iff_input_surjective a b c d j allowed).trans
    (InvariantProtection.square_surjective_iff
      (GradedMixedCompleteness.allEquiv a b c d allowed stable)
      (GradedMixedCompleteness.allEquiv a b (fun u => (c u).comp j)
        (fun u => (d u).comp j) allowed stable)
      _ _ (GradedCompletenessAllRestriction.extraction a b c d j allowed stable))

include stable in
theorem protected_iff_factors (n m : ℕ) : Protected a b c d j allowed n m ↔
    ∀ x : MixedContentOrbits.Selected (allowed n m), Function.Surjective
      (GradedCompletenessRestriction.factorMap a b c d j n m x.val) :=
  (protected_iff_residual_surjective a b c d j allowed stable n m).trans
    (InvariantProtection.family_surjective_iff
      (fun x : MixedContentOrbits.Selected (allowed n m) =>
        GradedCompletenessRestriction.factorMap a b c d j n m x.val))

omit [∀ n m v w, Decidable (allowed n m v w)] in
theorem all_protected_iff_finite_support_surjective :
    (∀ n m, Protected a b c d j allowed n m) ↔
    Function.Surjective (DFinsupp.mapRange.linearMap (fun z : ℕ × ℕ =>
      GradedCompletenessRestriction.selectedMap a b c d j z.1 z.2 (allowed z.1 z.2))) :=
  (all_protected_iff_input_surjective a b c d j allowed).trans
    (InvariantProtection.finite_support_surjective_iff _).symm

include stable in
theorem all_bounds_protected_iff (fw : P → ℕ) (bw : Q → ℕ) :
    (∀ D n m, Protected a b c d j
      (GradedMixedCompleteness.boundedAllowed allowed fw bw D) n m) ↔
    ∀ n m, Protected a b c d j allowed n m := by
  classical
  constructor
  · intro h n m
    apply (protected_iff_factors a b c d j allowed stable n m).mpr
    intro x
    let D := MixedContentGrading.engineering fw bw x.val.out.1 x.val.out.2
    let y : MixedContentOrbits.Selected
        (GradedMixedCompleteness.boundedAllowed allowed fw bw D n m) :=
      ⟨x.val, x.property, le_rfl⟩
    exact (protected_iff_factors a b c d j _
      (GradedMixedCompleteness.bounded_stable allowed stable fw bw D) n m).mp (h D n m) y
  · intro h D n m
    apply (protected_iff_factors a b c d j _
      (GradedMixedCompleteness.bounded_stable allowed stable fw bw D) n m).mpr
    intro x
    exact (protected_iff_factors a b c d j allowed stable n m).mp
      (h n m) ⟨x.val, x.property.1⟩

end
end Math.GradedSymmetryProtection
