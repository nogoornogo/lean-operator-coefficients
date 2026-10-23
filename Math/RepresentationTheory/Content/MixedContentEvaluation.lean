import Math.RepresentationTheory.Content.MixedContentOrbits

/-! Evaluation of content extraction on actual pure fields. -/
namespace Math.MixedContentOrbits
set_option autoImplicit false
noncomputable section
open Representation
variable {P Q H : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] [Group H]
  {V : P → Type*} {W : Q → Type*}
  [∀ u, AddCommGroup (V u)] [∀ u, Module ℂ (V u)]
  [∀ u, AddCommGroup (W u)] [∀ u, Module ℂ (W u)]
  (r : ∀ u, Representation ℂ H (V u)) (t : ∀ u, Representation ℂ H (W u))
  {n m : ℕ}

theorem equiv_apply (f : MixedWeightSupport.Coefficient
    (FiniteSpeciesExterior.representation r) (FiniteSpeciesExterior.representation t)
    (n := n) (m := m)) (x : Content (P := P) (Q := Q) (n := n) (m := m))
    (v : ∀ i, V (x.out.1 i)) (w : ∀ j, W (x.out.2 j)) :
    (equiv r t f x).val v w = f (MixedWeightSupport.pure
      (fun i => Pi.single (x.out.1 i) (v i)) (fun j => Pi.single (x.out.2 j) (w j))) := by
  classical
  change MixedSpeciesProjection.project (support x) f.toLinearMap
    (MixedWeightSupport.pure (fun i => Pi.single (x.out.1 i) (v i))
      (fun j => Pi.single (x.out.2 j) (w j))) = _
  rw [MixedSpeciesProjection.project_pure (support x) (stable x)]
  exact ite_eq_left ⟨⟨1,rfl⟩,⟨1,rfl⟩⟩

variable (allow : (Fin n → P) → (Fin m → Q) → Prop)
  [∀ p s, Decidable (allow p s)]
  (hs : ∀ p s (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin m)),
    allow (p ∘ e) (s ∘ f) ↔ allow p s)

theorem selectedEquiv_apply (f : MixedSpeciesProjection.supportSpace allow r t)
    (x : Selected allow) (v : ∀ i, V (x.val.out.1 i)) (w : ∀ j, W (x.val.out.2 j)) :
    (selectedEquiv r t allow hs f x).val v w = f.val (MixedWeightSupport.pure
      (fun i => Pi.single (x.val.out.1 i) (v i)) (fun j => Pi.single (x.val.out.2 j) (w j))) := by
  classical
  change MixedSpeciesProjection.project (support x.val) f.val.toLinearMap
    (MixedWeightSupport.pure (fun i => Pi.single (x.val.out.1 i) (v i))
      (fun j => Pi.single (x.val.out.2 j) (w j))) = _
  rw [MixedSpeciesProjection.project_pure (support x.val) (stable x.val)]
  exact ite_eq_left ⟨⟨1,rfl⟩,⟨1,rfl⟩⟩
end
end Math.MixedContentOrbits
