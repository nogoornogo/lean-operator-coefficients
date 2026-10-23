import Math.RepresentationTheory.Content.MixedContentOrbits
import Math.RepresentationTheory.Content.PositiveContentGrading

/-! Engineering and charge support decomposes at arbitrary mixed degrees. -/
namespace Math.MixedContentGrading
set_option autoImplicit false
noncomputable section
open scoped BigOperators
variable {P Q : Type*} {n m : ℕ}
  (fw : P → ℕ) (bw : Q → ℕ) (fq : P → ℤ) (bq : Q → ℤ)

def engineering (labels : Fin n → P) (scalars : Fin m → Q) : ℕ :=
  (∑ i, fw (labels i)) + ∑ j, bw (scalars j)

def charge (labels : Fin n → P) (scalars : Fin m → Q) : ℤ :=
  (∑ i, fq (labels i)) + ∑ j, bq (scalars j)

private theorem sum_perm {A : Type*} [AddCommMonoid A] {d : ℕ}
    (f : Fin d → A) (p : Equiv.Perm (Fin d)) : (∑ i, f (p i)) = ∑ i, f i :=
  Fintype.sum_equiv p _ _ (by intro i; rfl)

def selected (D : ℕ) (q : ℤ) (labels : Fin n → P) (scalars : Fin m → Q) : Prop :=
  engineering fw bw labels scalars ≤ D ∧ charge fq bq labels scalars = q

theorem stable (D : ℕ) (q : ℤ) (labels : Fin n → P) (scalars : Fin m → Q)
    (p : Equiv.Perm (Fin n)) (s : Equiv.Perm (Fin m)) :
    selected fw bw fq bq D q (labels ∘ p) (scalars ∘ s) ↔
      selected fw bw fq bq D q labels scalars := by
  simp only [selected, engineering, charge, Function.comp_apply,
    sum_perm (fun i => fw (labels i)) p, sum_perm (fun j => bw (scalars j)) s,
    sum_perm (fun i => fq (labels i)) p, sum_perm (fun j => bq (scalars j)) s]

section Coefficients
open Representation
variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {G : Type*} [Group G]
  {V : P → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module ℂ (V s)]
  {W : Q → Type*} [∀ s, AddCommGroup (W s)] [∀ s, Module ℂ (W s)]
  (r : ∀ s, Representation ℂ G (V s)) (t : ∀ s, Representation ℂ G (W s))

/-- Charge arithmetic restricts support; group invariance remains in every factor. -/
def equiv (D : ℕ) (q : ℤ) :
    MixedSpeciesProjection.supportSpace (selected fw bw fq bq D q (n := n) (m := m)) r t ≃ₗ[ℂ]
      (∀ c : MixedContentOrbits.Selected (selected fw bw fq bq D q (n := n) (m := m)),
        MixedPatternAssembly.orderedSpace r t c.val.out.1 c.val.out.2) := by
  classical
  exact MixedContentOrbits.selectedEquiv r t _ (stable fw bw fq bq D q)

end Coefficients
end
end Math.MixedContentGrading
