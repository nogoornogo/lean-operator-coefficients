import GUT.SU5.Representations.Matter
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype

/-! Diagonal signs and determinant-corrected permutations in the actual SU(5). -/

set_option autoImplicit false

namespace GUT.SU5.MonomialElements

noncomputable section

open StandardModelEmbedding Matter

def signAt (i j : Fin 5) : ℂ := if j = i then 1 else -1

def diagonalSign (i : Fin 5) : TargetGroup :=
  ⟨Matrix.diagonal (signAt i), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext a b
      by_cases hab : a = b
      · subst b
        by_cases hai : a = i <;>
          simp [signAt, hai]
      · simp [hab]
    · rw [Matrix.det_diagonal]
      have h : ∀ i : Fin 5, (∏ j : Fin 5, if j = i then (1 : ℤ) else -1) = 1 := by
        decide
      simpa [signAt] using congrArg (fun z : ℤ => (z : ℂ)) (h i)⟩

@[simp] theorem diagonalSign_inv (i : Fin 5) : (diagonalSign i)⁻¹ = diagonalSign i := by
  apply Subtype.ext
  change (Matrix.diagonal (signAt i)).conjTranspose = Matrix.diagonal (signAt i)
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : j = i <;> simp [signAt, h]

theorem diagonalSign_action (i : Fin 5) (v : Five) :
    fundamental (diagonalSign i) v = fun j => signAt i j * v j := by
  ext j
  simp [fundamental, diagonalSign, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

def signedPermutation (p : Equiv.Perm (Fin 5)) : TargetGroup :=
  if hp : Equiv.Perm.sign p = 1 then
    ⟨p.permMatrix ℂ, by
      rw [Matrix.mem_specialUnitaryGroup_iff]
      constructor
      · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
        simp
      · simp [hp]⟩
  else
    ⟨-(p.permMatrix ℂ), by
      have hn : Equiv.Perm.sign p = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
        · exact (hp h).elim
        · exact h
      rw [Matrix.mem_specialUnitaryGroup_iff]
      constructor
      · rw [Matrix.mem_unitaryGroup_iff, star_neg, neg_mul_neg,
          Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
          ← Matrix.permMatrix_mul]
        simp
      · norm_num [Matrix.det_neg, hn]⟩

def permutationSign (p : Equiv.Perm (Fin 5)) : ℂ :=
  if Equiv.Perm.sign p = 1 then 1 else -1

theorem permutationSign_ne_zero (p : Equiv.Perm (Fin 5)) : permutationSign p ≠ 0 := by
  simp [permutationSign]
  split_ifs <;> norm_num

theorem signedPermutation_action (p : Equiv.Perm (Fin 5)) (v : Five) :
    fundamental (signedPermutation p) v = permutationSign p • (v ∘ p) := by
  by_cases hp : Equiv.Perm.sign p = 1 <;>
    simp [fundamental, signedPermutation, permutationSign, hp,
      Matrix.toLin'_apply, Matrix.permMatrix_mulVec]

end

end GUT.SU5.MonomialElements
