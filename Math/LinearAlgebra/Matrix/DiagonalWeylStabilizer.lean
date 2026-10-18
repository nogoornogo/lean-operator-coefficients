import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

/-! Classification of diagonal-vacuum preservation by phase/permutation matrices.
This does not classify all group automorphisms or all vacuum stabilizers. -/
namespace Math.DiagonalWeylStabilizer
set_option autoImplicit false
noncomputable section
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Permutation matrices use the mathlib row-permutation convention. -/
theorem permutation_conjugate (s : Equiv.Perm n) (d : n → ℂ) :
    s.permMatrix ℂ * Matrix.diagonal d * Equiv.Perm.permMatrix ℂ s.symm =
      Matrix.diagonal (d ∘ s) := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases h : i = j
  · subst j; simp [Matrix.submatrix, Matrix.diagonal]
  · simp [Matrix.submatrix, Matrix.diagonal, h]

/-- Arbitrary unit-modulus diagonal phases followed by a permutation. -/
def representative (s : Equiv.Perm n) (u : n → Circle) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => (u i : ℂ)) * s.permMatrix ℂ

theorem representative_conjugate (s : Equiv.Perm n) (u : n → Circle) (d : n → ℂ) :
    representative s u * Matrix.diagonal d * star (representative s u) =
      Matrix.diagonal (d ∘ s) := by
  have hp : star (s.permMatrix ℂ) = Equiv.Perm.permMatrix ℂ s.symm := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rfl
  unfold representative
  rw [star_mul, hp]
  calc
    _ = Matrix.diagonal (fun i => (u i : ℂ)) *
        (s.permMatrix ℂ * Matrix.diagonal d * Equiv.Perm.permMatrix ℂ s.symm) *
        star (Matrix.diagonal (fun i => (u i : ℂ))) := by noncomm_ring
    _ = Matrix.diagonal (d ∘ s) := by
      rw [permutation_conjugate, star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      change (u i : ℂ) * d (s i) * (starRingEnd ℂ) (u i : ℂ) = d (s i)
      have hu : (u i : ℂ) * (starRingEnd ℂ) (u i : ℂ) = 1 := by
        rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
      calc
        _ = d (s i) * ((u i : ℂ) * (starRingEnd ℂ) (u i : ℂ)) := by ring
        _ = d (s i) := by rw [hu, mul_one]

/-- Complete preservation test within the phase/permutation family. -/
theorem fixed_iff (s : Equiv.Perm n) (u : n → Circle) (d : n → ℂ) :
    representative s u * Matrix.diagonal d * star (representative s u) =
      Matrix.diagonal d ↔ ∀ i, d (s i) = d i := by
  rw [representative_conjugate]
  constructor
  · intro he i
    simpa using congrArg (fun m : Matrix n n ℂ => m i i) he
  · intro he
    congr 1
    exact funext he
/-- Eigenvalue-preserving permutations form the classified subgroup. -/
def preserving (d : n → ℂ) : Subgroup (Equiv.Perm n) where
  carrier := {s | ∀ i, d (s i) = d i}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro s t hs ht i
    change d (s (t i)) = d i
    rw [hs, ht]
  inv_mem' := by
    intro s hs i
    have he := hs (s.symm i)
    simpa using he.symm

theorem fixed_iff_mem (s : Equiv.Perm n) (u : n → Circle) (d : n → ℂ) :
    representative s u * Matrix.diagonal d * star (representative s u) =
      Matrix.diagonal d ↔ s ∈ preserving d := fixed_iff s u d

omit [Fintype n] in
/-- A nondegenerate singleton split is preserved iff its unique coordinate is fixed. -/
theorem split_preserves_iff (s : Equiv.Perm n) (j : n) (a b : ℂ) (hab : a ≠ b) :
    (∀ i, (if s i = j then b else a) = (if i = j then b else a)) ↔ s j = j := by
  constructor
  · intro h
    by_contra hn
    have he := h j
    simp [hn] at he
    exact hab he
  · intro hj i
    by_cases hi : i = j
    · subst i; simp [hj]
    · have hsi : s i ≠ j := by
        intro he
        exact hi (s.injective (he.trans hj.symm))
      simp [hi, hsi]

end
end Math.DiagonalWeylStabilizer
