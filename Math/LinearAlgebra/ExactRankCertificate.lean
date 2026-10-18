import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! Exact finite rank certificates, stable under field homomorphisms. -/
namespace Math.ExactRankCertificate
set_option autoImplicit false
open Matrix
variable {K L I J T : Type*} [Field K] [Field L]
  [Fintype I] [Fintype J] [Fintype T] [DecidableEq T]

/-- Rank factorization with both independence and spanning certified by inverses. -/
structure Certificate (A : Matrix I J K) where
  columns : Matrix I T K
  rows : Matrix T J K
  left : Matrix T I K
  right : Matrix J T K
  factor : A = columns * rows
  left_inverse : left * columns = 1
  right_inverse : rows * right = 1

theorem rank_eq {A : Matrix I J K} (c : Certificate (T := T) A) :
    A.rank = Fintype.card T := by
  apply le_antisymm
  · rw [c.factor]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  · have he : c.left * A * c.right = 1 := by
      calc
        _ = c.left * (c.columns * c.rows) * c.right := congrArg (fun M => c.left * M * c.right) c.factor
        _ = 1 := by rw [← Matrix.mul_assoc c.left, c.left_inverse, Matrix.one_mul, c.right_inverse]
    have h := (Matrix.rank_mul_le_left (c.left * A) c.right).trans
      (Matrix.rank_mul_le_right c.left A)
    rwa [he, Matrix.rank_one] at h

def map {A : Matrix I J K} (c : Certificate (T := T) A) (f : K →+* L) :
    Certificate (T := T) (A.map f) where
  columns := c.columns.map f
  rows := c.rows.map f
  left := c.left.map f
  right := c.right.map f
  factor := by simpa only [Matrix.map_mul] using congrArg (fun M => M.map f) c.factor
  left_inverse := by rw [← Matrix.map_mul, c.left_inverse]; simp
  right_inverse := by rw [← Matrix.map_mul, c.right_inverse]; simp

theorem mapped_rank {A : Matrix I J K} (c : Certificate (T := T) A) (f : K →+* L) :
    (A.map f).rank = Fintype.card T := rank_eq (map c f)

theorem mapped_nullity {A : Matrix I J K} (c : Certificate (T := T) A) (f : K →+* L) :
    Module.finrank L (LinearMap.ker (A.map f).mulVecLin) = Fintype.card J - Fintype.card T := by
  have h := LinearMap.finrank_range_add_finrank_ker (A.map f).mulVecLin
  have hr := mapped_rank c f
  change (A.map f).rank + Module.finrank L (LinearMap.ker (A.map f).mulVecLin) = _ at h
  rw [hr, Module.finrank_pi] at h
  omega

/-- Build a certificate from reconstruction identities on arbitrary vectors. -/
noncomputable def Certificate.ofActions [DecidableEq I] [DecidableEq J]
    (A : Matrix I J K)
    (E : (T → K) →ₗ[K] (I → K)) (R : (J → K) →ₗ[K] (T → K))
    (P : (I → K) →ₗ[K] (T → K)) (S : (T → K) →ₗ[K] (J → K))
    (hf : ∀ v, E (R v) = A *ᵥ v)
    (hl : ∀ u, P (E u) = u) (hr : ∀ u, R (S u) = u) : Certificate (T := T) A where
  columns := LinearMap.toMatrix' E
  rows := LinearMap.toMatrix' R
  left := LinearMap.toMatrix' P
  right := LinearMap.toMatrix' S
  factor := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact (hf v).symm
  left_inverse := by
    apply Matrix.mulVec_injective
    funext u
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec,
      Matrix.one_mulVec]
    exact hl u
  right_inverse := by
    apply Matrix.mulVec_injective
    funext u
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec,
      Matrix.one_mulVec]
    exact hr u

/-- The third row and column are sums of the first two. -/
def exampleMatrix : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,1; 0,1,1; 1,1,2]

private def extendPair : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun u := ![u 0, u 1, u 0 + u 1]
  map_add' u v := by ext i; fin_cases i <;> (simp; all_goals ring)
  map_smul' a u := by ext i; fin_cases i <;> (simp; all_goals ring)

private def readPair : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun v := ![v 0 + v 2, v 1 + v 2]
  map_add' u v := by ext i; fin_cases i <;> (simp; all_goals ring)
  map_smul' a u := by ext i; fin_cases i <;> (simp; all_goals ring)

private def projectPair : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun v := ![v 0, v 1]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

private def insertPair : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun u := ![u 0, u 1, 0]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp

noncomputable def exampleCertificate : Certificate (T := Fin 2) exampleMatrix :=
  Certificate.ofActions exampleMatrix extendPair readPair projectPair insertPair
    (by intro v; ext i; fin_cases i <;>
        simp [extendPair, readPair, exampleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; all_goals ring)
    (by intro u; ext i; fin_cases i <;> simp [projectPair, extendPair])
    (by intro u; ext i; fin_cases i <;> simp [readPair, insertPair])

theorem example_complex_rank : (exampleMatrix.map (Rat.castHom ℂ)).rank = 2 :=
  mapped_rank exampleCertificate (Rat.castHom ℂ)

end Math.ExactRankCertificate
