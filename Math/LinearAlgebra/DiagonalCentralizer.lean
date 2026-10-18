import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic

/-! Exact diagonal commutants. Distinct eigenvalues prohibit mixed entries;
equal eigenvalues do not impose an artificial block restriction. -/
namespace Math.DiagonalCentralizer
set_option autoImplicit false
variable {k I J N : Type*} [Field k]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype N] [DecidableEq N]

theorem commute_iff (A : Matrix N N k) (d : N → k) :
    A * Matrix.diagonal d = Matrix.diagonal d * A ↔
      ∀ i j, d i ≠ d j → A i j = 0 := by
  constructor
  · intro h i j hij
    have he := congrArg (fun M : Matrix N N k => M i j) h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hz : (d i - d j) * A i j = 0 := by linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij)
  · intro h
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

def eigenvalues (a b : k) : I ⊕ J → k := Sum.elim (fun _ => a) (fun _ => b)

theorem two_eigenvalue_iff (A : Matrix (I ⊕ J) (I ⊕ J) k) (a b : k) (hab : a ≠ b) :
    A * Matrix.diagonal (eigenvalues a b) = Matrix.diagonal (eigenvalues a b) * A ↔
      (∀ i j, A (.inl i) (.inr j) = 0) ∧
      (∀ j i, A (.inr j) (.inl i) = 0) := by
  rw [commute_iff]
  constructor
  · intro h
    exact ⟨fun i j => h _ _ hab, fun j i => h _ _ (Ne.symm hab)⟩
  · rintro ⟨hlr, hrl⟩ i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hlr _ _
    · exact hrl _ _
    · exact (hij rfl).elim

theorem block_form_iff (A : Matrix (I ⊕ J) (I ⊕ J) k) (a b : k) (hab : a ≠ b) :
    A * Matrix.diagonal (eigenvalues a b) = Matrix.diagonal (eigenvalues a b) * A ↔
      A = Matrix.fromBlocks A.toBlocks₁₁ 0 0 A.toBlocks₂₂ := by
  rw [two_eigenvalue_iff A a b hab]
  constructor
  · rintro ⟨hlr, hrl⟩
    ext i j
    cases i <;> cases j
    · rfl
    · exact hlr _ _
    · exact hrl _ _
    · rfl
  · intro h
    constructor
    · intro i j; simpa using congrArg (fun M => M (.inl i) (.inr j)) h
    · intro j i; simpa using congrArg (fun M => M (.inr j) (.inl i)) h

theorem collision (A : Matrix (I ⊕ J) (I ⊕ J) k) (a : k) :
    A * Matrix.diagonal (eigenvalues (I := I) (J := J) a a) =
      Matrix.diagonal (eigenvalues a a) * A := by
  rw [commute_iff]
  intro i j hij
  have he : eigenvalues (I := I) (J := J) a a i = eigenvalues a a j := by
    cases i <;> cases j <;> rfl
  exact (hij he).elim
end Math.DiagonalCentralizer
