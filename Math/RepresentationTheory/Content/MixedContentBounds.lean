import Math.RepresentationTheory.Content.MixedContentGrading
import Mathlib.Data.Fintype.Sigma

/-! Positive weights give finitely many permutation contents under every bound. -/
namespace Math.MixedContentBounds
set_option autoImplicit false
noncomputable section
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  (fw : P → ℕ) (bw : Q → ℕ) (hf : ∀ u, 0 < fw u) (hb : ∀ u, 0 < bw u)

abbrev Content := Σ z : ℕ × ℕ, MixedContentOrbits.Content (P := P) (Q := Q) (n := z.1) (m := z.2)
def engineering (x : Content (P := P) (Q := Q)) :=
  MixedContentGrading.engineering fw bw x.2.out.1 x.2.out.2

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
include hf hb in
theorem slots_le {n m : ℕ} (v : Fin n → P) (w : Fin m → Q) :
    n + m ≤ MixedContentGrading.engineering fw bw v w := by
  have hn : n ≤ ∑ i, fw (v i) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (show (1 : ℕ) ≤ fw (v i) from hf (v i)))
  have hm : m ≤ ∑ j, bw (w j) := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      (show (1 : ℕ) ≤ bw (w j) from hb (w j)))
  exact Nat.add_le_add hn hm

omit [DecidableEq P] [DecidableEq Q] in
include hf hb in
theorem bounded_finite (D : ℕ) :
    {x : Content (P := P) (Q := Q) | engineering fw bw x ≤ D}.Finite := by
  let I := Σ n : Fin (D+1), Σ m : Fin (D+1),
    MixedContentOrbits.Content (P := P) (Q := Q) (n := n.val) (m := m.val)
  let embed : I → Content (P := P) (Q := Q) := fun x => ⟨(x.1.val, x.2.1.val), x.2.2⟩
  apply (Set.finite_range embed).subset
  intro x hx
  have hs : x.1.1 + x.1.2 ≤ D := (slots_le fw bw hf hb x.2.out.1 x.2.out.2).trans hx
  exact ⟨⟨⟨x.1.1, Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) hs)⟩,
    ⟨⟨x.1.2, Nat.lt_succ_of_le (le_trans (Nat.le_add_left _ _) hs)⟩, x.2⟩⟩, rfl⟩

end
end Math.MixedContentBounds
