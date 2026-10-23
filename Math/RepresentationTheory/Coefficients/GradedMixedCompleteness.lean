import Math.RepresentationTheory.Constructions.TypedMixedSeparatedHom
import Math.RepresentationTheory.Content.MixedContentGrading
import Math.RepresentationTheory.Invariants.DirectSumFunctionalProduct
import Math.LinearAlgebra.Constructions.ProductZeroCriteria

/-! Content-wise residual Hom completeness at arbitrary mixed degrees and supports. -/
namespace Math.GradedMixedCompleteness
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {P Q G H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Group G] [Group H]
  {L M : P → Type*} {K N : Q → Type*}
  [∀ u, AddCommGroup (L u)] [∀ u, Module ℂ (L u)]
  [∀ u, AddCommGroup (M u)] [∀ u, Module ℂ (M u)]
  [∀ u, AddCommGroup (K u)] [∀ u, Module ℂ (K u)]
  [∀ u, AddCommGroup (N u)] [∀ u, Module ℂ (N u)]
  (a : ∀ u, Representation ℂ G (L u)) (b : ∀ u, Representation ℂ G (K u))
  (c : ∀ u, Representation ℂ H (M u)) (d : ∀ u, Representation ℂ H (N u))
  (n m : ℕ)

abbrev Content := MixedContentOrbits.Content (P := P) (Q := Q) (n := n) (m := m)
abbrev Factor (x : Content (P := P) (Q := Q) n m) :=
  IntertwiningMap (TypedMixedSeparatedHom.residual a b c d x.out.1 x.out.2) (trivial ℂ H ℂ)
abbrev Input := MixedWeightSupport.Coefficient
  (FiniteSpeciesExterior.representation (TypedMixedSeparatedHom.fieldF a c))
  (FiniteSpeciesExterior.representation (TypedMixedSeparatedHom.fieldB b d)) (n := n) (m := m)

def equiv : Input a b c d n m ≃ₗ[ℂ] (∀ x : Content (P := P) (Q := Q) n m, Factor a b c d n m x) :=
  (MixedContentOrbits.equiv (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d)).trans
    (LinearEquiv.piCongrRight fun x => TypedMixedSeparatedHom.equiv a b c d x.out.1 x.out.2)

section Selection
variable (allow : (Fin n → P) → (Fin m → Q) → Prop)
  [∀ labels scalars, Decidable (allow labels scalars)]
  (stableAllow : ∀ labels scalars (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
    allow (labels ∘ p) (scalars ∘ q) ↔ allow labels scalars)

def selectedEquiv : MixedSpeciesProjection.supportSpace allow
    (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d) ≃ₗ[ℂ]
    (∀ x : MixedContentOrbits.Selected allow, Factor a b c d n m x.val) :=
  (MixedContentOrbits.selectedEquiv (TypedMixedSeparatedHom.fieldF a c)
    (TypedMixedSeparatedHom.fieldB b d) allow stableAllow).trans
    (LinearEquiv.piCongrRight fun x => TypedMixedSeparatedHom.equiv a b c d x.val.out.1 x.val.out.2)

include stableAllow in
theorem selected_forbidden_iff :
    (∀ f : MixedSpeciesProjection.supportSpace allow
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ↔
    ∀ x : MixedContentOrbits.Selected allow, ∀ q : Factor a b c d n m x.val, q = 0 :=
  ProductZeroCriteria.forbidden_iff (k := ℂ)
    (I := MixedContentOrbits.Selected allow) (V := fun x => Factor a b c d n m x.val)
    (selectedEquiv a b c d n m allow stableAllow)

include stableAllow in
theorem selected_nonzero_iff :
    (∃ f : MixedSpeciesProjection.supportSpace allow
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f ≠ 0) ↔
    ∃ x : MixedContentOrbits.Selected allow, ∃ q : Factor a b c d n m x.val, q ≠ 0 := by
  simpa only [not_forall, not_not] using
    not_congr (selected_forbidden_iff a b c d n m allow stableAllow)
end Selection

section AllDegrees
variable (allowed : ∀ n m : ℕ, (Fin n → P) → (Fin m → Q) → Prop)
  [∀ n m v w, Decidable (allowed n m v w)]
  (stableAllowed : ∀ n m v w (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)),
    allowed n m (v ∘ p) (w ∘ q) ↔ allowed n m v w)

abbrev AllIndex := Σ z : ℕ × ℕ, MixedContentOrbits.Selected (allowed z.1 z.2)
abbrev allResidual (x : AllIndex allowed) :=
  TypedMixedSeparatedHom.residual a b c d x.2.val.out.1 x.2.val.out.2

def allEquiv :
    (∀ z : ℕ × ℕ, MixedSpeciesProjection.supportSpace (allowed z.1 z.2)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d)) ≃ₗ[ℂ]
    IntertwiningMap (Representation.directSum (allResidual a b c d allowed)) (trivial ℂ H ℂ) := by
  classical
  exact (LinearEquiv.piCongrRight (fun z : ℕ × ℕ =>
    selectedEquiv a b c d z.1 z.2 (allowed z.1 z.2) (stableAllowed z.1 z.2))).trans
    ((LinearEquiv.piCurry ℂ (fun z : ℕ × ℕ =>
      fun x : MixedContentOrbits.Selected (allowed z.1 z.2) => Factor a b c d z.1 z.2 x.val)).symm.trans
      (DirectSumFunctionalProduct.equiv (I := AllIndex allowed) (H := H)
        (V := fun x => TypedMixedSeparatedHom.Carrier a b c d x.2.val.out.1 x.2.val.out.2)
        (allResidual a b c d allowed)).symm)

include stableAllowed in
theorem all_forbidden_iff :
    (∀ f : IntertwiningMap (Representation.directSum (allResidual a b c d allowed))
      (trivial ℂ H ℂ), f = 0) ↔
    ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0 := by
  classical
  rw [DirectSumFunctionalProduct.forbidden_iff (I := AllIndex allowed) (H := H)
    (V := fun x => TypedMixedSeparatedHom.Carrier a b c d x.2.val.out.1 x.2.val.out.2)
    (allResidual a b c d allowed)]
  constructor
  · intro h n m
    exact (selected_forbidden_iff a b c d n m (allowed n m) (stableAllowed n m)).mpr
      (fun x => h ⟨(n,m),x⟩)
  · intro h x
    exact (selected_forbidden_iff a b c d x.1.1 x.1.2 (allowed x.1.1 x.1.2)
      (stableAllowed x.1.1 x.1.2)).mp (h x.1.1 x.1.2) x.2

include stableAllowed in
theorem all_nonzero_iff :
    (∃ f : IntertwiningMap (Representation.directSum (allResidual a b c d allowed))
      (trivial ℂ H ℂ), f ≠ 0) ↔
    ∃ n m, ∃ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f ≠ 0 := by
  simpa only [not_forall, not_not] using
    not_congr (all_forbidden_iff a b c d allowed stableAllowed)

variable (fw : P → ℕ) (bw : Q → ℕ)
def boundedAllowed (D n m : ℕ) (v : Fin n → P) (w : Fin m → Q) :=
  allowed n m v w ∧ MixedContentGrading.engineering fw bw v w ≤ D

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [∀ n m v w, Decidable (allowed n m v w)] in
include stableAllowed in
theorem bounded_stable (D n m : ℕ) (v : Fin n → P) (w : Fin m → Q)
    (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin m)) :
    boundedAllowed allowed fw bw D n m (v ∘ p) (w ∘ q) ↔
      boundedAllowed allowed fw bw D n m v w := by
  apply and_congr (stableAllowed n m v w p q)
  simpa [MixedContentGrading.selected, MixedContentGrading.charge] using
    MixedContentGrading.stable fw bw (fun _ => 0) (fun _ => 0) D 0 v w p q

include stableAllowed in
theorem all_bounds_forbidden_iff :
    (∀ D n m, ∀ f : MixedSpeciesProjection.supportSpace (boundedAllowed allowed fw bw D n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0) ↔
    ∀ n m, ∀ f : MixedSpeciesProjection.supportSpace (allowed n m)
      (TypedMixedSeparatedHom.fieldF a c) (TypedMixedSeparatedHom.fieldB b d), f = 0 := by
  classical
  constructor
  · intro h n m
    apply (selected_forbidden_iff a b c d n m (allowed n m) (stableAllowed n m)).mpr
    intro x q
    let D := MixedContentGrading.engineering fw bw x.val.out.1 x.val.out.2
    let y : MixedContentOrbits.Selected (boundedAllowed allowed fw bw D n m) :=
      ⟨x.val, x.property, le_rfl⟩
    exact (selected_forbidden_iff a b c d n m (boundedAllowed allowed fw bw D n m)
      (bounded_stable allowed stableAllowed fw bw D n m)).mp (h D n m) y q
  · intro h D n m
    apply (selected_forbidden_iff a b c d n m (boundedAllowed allowed fw bw D n m)
      (bounded_stable allowed stableAllowed fw bw D n m)).mpr
    intro x q
    exact (selected_forbidden_iff a b c d n m (allowed n m) (stableAllowed n m)).mp
      (h n m) ⟨x.val, x.property.1⟩ q
end AllDegrees

end
end Math.GradedMixedCompleteness
