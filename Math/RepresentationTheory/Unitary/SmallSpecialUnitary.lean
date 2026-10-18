import Math.RepresentationTheory.Decomposition.BasisIrreducibility
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-! Irreducibility of the defining SU(2) and SU(3) actions, using explicit
diagonal elements and basis-mixing matrices. -/

namespace Math.SmallSpecialUnitary
noncomputable section
open Matrix

def defining (n : ℕ) : Representation ℂ (specialUnitaryGroup (Fin n) ℂ) (Fin n → ℂ) where
  toFun g := Matrix.toLin' g.val
  map_one' := Matrix.toLin'_one
  map_mul' _ _ := Matrix.toLin'_mul _ _

def signAt (i j : Fin 3) : ℂ := if j = i then 1 else -1

def diagonalSign (i : Fin 3) : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal (signAt i), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      ext a b
      by_cases hab : a = b
      · subst b
        by_cases hai : a = i <;> simp [signAt, hai]
      · simp [hab]
    · rw [Matrix.det_diagonal]
      have h : ∀ i : Fin 3, (∏ j : Fin 3, if j = i then (1 : ℤ) else -1) = 1 := by
        decide
      simpa [signAt] using congrArg (fun z : ℤ => (z : ℂ)) (h i)⟩

def signedPermutation (p : Equiv.Perm (Fin 3)) : specialUnitaryGroup (Fin 3) ℂ :=
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

theorem defining_three_irreducible : (defining 3).IsIrreducible := by
  let b := Pi.basisFun ℂ (Fin 3)
  apply Math.RepresentationTheory.irreducible_of_basis_coordinates (defining 3) b
  · intro S v hv i
    have he : v + defining 3 (diagonalSign i) v = (2 * b.repr v i) • b i := by
      ext j
      by_cases h : j = i <;>
        simp [defining, diagonalSign, Matrix.toLin'_apply, Matrix.mulVec_diagonal,
          b, Pi.basisFun_apply, signAt, h, two_mul]
    have hm := S.toSubmodule.smul_mem (2 : ℂ)⁻¹
      (S.toSubmodule.add_mem hv (S.apply_mem_toSubmodule (diagonalSign i) hv))
    rw [he] at hm
    change b.repr v i • b i ∈ S.toSubmodule
    simpa [smul_smul] using hm
  · intro i j
    refine ⟨signedPermutation (Equiv.swap i j), ?_⟩
    by_cases hp : Equiv.Perm.sign (Equiv.swap i j) = 1
    · simp only [signedPermutation, dite_eq_left hp]
      simp [defining, Matrix.toLin'_apply, b, Pi.basisFun_apply]
    · simp only [signedPermutation, dite_eq_right hp]
      simp [defining, Matrix.toLin'_apply, b, Pi.basisFun_apply]

def phaseTwo : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

def flipTwo : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

theorem defining_two_irreducible : (defining 2).IsIrreducible := by
  let b := Pi.basisFun ℂ (Fin 2)
  apply Math.RepresentationTheory.irreducible_of_basis_coordinates (defining 2) b
  · intro S v hv i
    let c : ℂ := if i = 0 then Complex.I else -Complex.I
    have he : v - c • defining 2 phaseTwo v = (2 * b.repr v i) • b i := by
      ext j
      fin_cases i <;> fin_cases j <;>
        simp [defining, phaseTwo, Matrix.toLin'_apply,
          dotProduct, Fin.sum_univ_two, b, Pi.basisFun_apply, c, ← mul_assoc, two_mul]
    have hm := S.toSubmodule.smul_mem (2 : ℂ)⁻¹
      (S.toSubmodule.sub_mem hv (S.toSubmodule.smul_mem c
        (S.apply_mem_toSubmodule phaseTwo hv)))
    rw [he] at hm
    change b.repr v i • b i ∈ S.toSubmodule
    simpa [smul_smul] using hm
  · intro i j
    by_cases h : i = j
    · subst j
      exact ⟨1, by simp⟩
    · refine ⟨flipTwo, ?_⟩
      fin_cases i <;> fin_cases j <;>
        simp_all [defining, flipTwo, Matrix.toLin'_apply, b, Pi.basisFun_apply]

end
end Math.SmallSpecialUnitary
