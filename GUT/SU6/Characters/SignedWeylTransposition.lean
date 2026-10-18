import GUT.SU6.Characters.WeylMatrix

/-!
# Signed representatives of arbitrary SU(6) Weyl transpositions

Every coordinate transposition has an ordinary permutation matrix of
determinant `-1`.  Multiplying on the left by a diagonal matrix with one `-1`
entry produces an element of `SU(6)`.  The diagonal sign disappears when this
matrix conjugates a diagonal torus element, so the resulting Weyl action is
the pure coordinate transposition.

`GUT.WeylMatrix` contains the original concrete `(3 6)` instance.  This
module packages the same construction uniformly so that other hypercharge
subtori can use their own normalizing transpositions.
-/

namespace GUT
namespace SignedWeylTransposition

open Matrix

abbrev I6 := WeylMatrix.I6

def transposition (a b : I6) : Equiv.Perm I6 :=
  Equiv.swap a b

@[simp]
theorem transposition_symm (a b : I6) :
    (transposition a b).symm = transposition a b := by
  simp [transposition]

def signAt (a i : I6) : ℂ :=
  if i = a then -1 else 1

def signMatrix (a : I6) : Matrix I6 I6 ℂ :=
  Matrix.diagonal (signAt a)

def permutationMatrix (a b : I6) : Matrix I6 I6 ℂ :=
  (transposition a b).permMatrix ℂ

def signedMatrix (a b : I6) : Matrix I6 I6 ℂ :=
  signMatrix a * permutationMatrix a b

def signedMatrixInv (a b : I6) : Matrix I6 I6 ℂ :=
  permutationMatrix a b * signMatrix a

@[simp]
theorem signAt_sq (a i : I6) : signAt a i * signAt a i = 1 := by
  by_cases h : i = a <;> simp [signAt, h]

@[simp]
theorem star_signAt (a i : I6) : star (signAt a i) = signAt a i := by
  by_cases h : i = a <;> simp [signAt, h]

theorem signMatrix_mul_self (a : I6) :
    signMatrix a * signMatrix a = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [signMatrix]
  · simp [signMatrix, h]

theorem permutationMatrix_mul_self (a b : I6) :
    permutationMatrix a b * permutationMatrix a b = 1 := by
  change
    (transposition a b).permMatrix ℂ *
        (transposition a b).permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul (R := ℂ)]
  simp [transposition]

theorem signedMatrix_mul_inv (a b : I6) :
    signedMatrix a b * signedMatrixInv a b = 1 := by
  rw [signedMatrix, signedMatrixInv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (permutationMatrix a b)
    (permutationMatrix a b) (signMatrix a)]
  rw [← Matrix.mul_assoc (signMatrix a)
    (permutationMatrix a b * permutationMatrix a b) (signMatrix a)]
  rw [permutationMatrix_mul_self]
  simp [signMatrix_mul_self]

theorem signedMatrix_inv_mul (a b : I6) :
    signedMatrixInv a b * signedMatrix a b = 1 := by
  rw [signedMatrix, signedMatrixInv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (signMatrix a) (signMatrix a)
    (permutationMatrix a b)]
  rw [← Matrix.mul_assoc (permutationMatrix a b)
    (signMatrix a * signMatrix a) (permutationMatrix a b)]
  rw [signMatrix_mul_self]
  simp [permutationMatrix_mul_self]

theorem det_signMatrix (a : I6) : Matrix.det (signMatrix a) = -1 := by
  rw [signMatrix, Matrix.det_diagonal, Fintype.prod_eq_mul_prod_compl a]
  simp [signAt]

theorem det_permutationMatrix (a b : I6) (h : a ≠ b) :
    Matrix.det (permutationMatrix a b) = -1 := by
  rw [permutationMatrix, Matrix.det_permutation]
  rw [transposition, Equiv.Perm.sign_swap h]
  norm_num

theorem det_signedMatrix (a b : I6) (h : a ≠ b) :
    Matrix.det (signedMatrix a b) = 1 := by
  rw [signedMatrix, Matrix.det_mul, det_signMatrix,
    det_permutationMatrix a b h]
  norm_num

theorem permutation_conj_diagonal (a b : I6) (d : I6 → ℂ) :
    permutationMatrix a b * Matrix.diagonal d * permutationMatrix a b =
      Matrix.diagonal (d ∘ transposition a b) := by
  rw [permutationMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.submatrix, Matrix.diagonal]
  · simp [Matrix.submatrix, Matrix.diagonal, hij]

theorem signMatrix_conj_diagonal (a : I6) (d : I6 → ℂ) :
    signMatrix a * Matrix.diagonal d * signMatrix a =
      Matrix.diagonal d := by
  rw [signMatrix, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [mul_comm, mul_left_comm]
  · simp [h]

theorem signed_conj_diagonal (a b : I6) (d : I6 → ℂ) :
    signedMatrix a b * Matrix.diagonal d * signedMatrixInv a b =
      Matrix.diagonal (d ∘ transposition a b) := by
  calc
    signedMatrix a b * Matrix.diagonal d * signedMatrixInv a b =
        signMatrix a *
            (permutationMatrix a b * Matrix.diagonal d *
              permutationMatrix a b) *
          signMatrix a := by
      simp only [signedMatrix, signedMatrixInv]
      noncomm_ring
    _ = signMatrix a * Matrix.diagonal (d ∘ transposition a b) *
          signMatrix a := by
      rw [permutation_conj_diagonal]
    _ = Matrix.diagonal (d ∘ transposition a b) :=
      signMatrix_conj_diagonal a (d ∘ transposition a b)

theorem star_signMatrix (a : I6) : star (signMatrix a) = signMatrix a := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [signMatrix]
  · simp [signMatrix, h, Ne.symm h]

theorem star_permutationMatrix (a b : I6) :
    star (permutationMatrix a b) = permutationMatrix a b := by
  rw [permutationMatrix, star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix]
  simp [transposition]

theorem star_signedMatrix (a b : I6) :
    star (signedMatrix a b) = signedMatrixInv a b := by
  rw [signedMatrix, signedMatrixInv, star_mul, star_signMatrix,
    star_permutationMatrix]

theorem signedMatrix_mem_specialUnitary (a b : I6) (h : a ≠ b) :
    signedMatrix a b ∈ Matrix.specialUnitaryGroup I6 ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, star_signedMatrix]
    exact signedMatrix_mul_inv a b
  · exact det_signedMatrix a b h

def signedTranspositionSU (a b : I6) (h : a ≠ b) :
    Matrix.specialUnitaryGroup I6 ℂ :=
  ⟨signedMatrix a b, signedMatrix_mem_specialUnitary a b h⟩

@[simp]
theorem coe_signedTranspositionSU (a b : I6) (h : a ≠ b) :
    ((signedTranspositionSU a b h : Matrix.specialUnitaryGroup I6 ℂ) :
        Matrix I6 I6 ℂ) = signedMatrix a b :=
  rfl

theorem coe_signedTranspositionSU_inv (a b : I6) (h : a ≠ b) :
    ((signedTranspositionSU a b h)⁻¹ :
        Matrix.specialUnitaryGroup I6 ℂ) =
      signedMatrixInv a b := by
  change star (signedMatrix a b) = signedMatrixInv a b
  exact star_signedMatrix a b

theorem signedTranspositionSU_conj_diagonal
    (a b : I6) (h : a ≠ b) (d : I6 → ℂ) :
    ((signedTranspositionSU a b h : Matrix.specialUnitaryGroup I6 ℂ) :
          Matrix I6 I6 ℂ) *
        Matrix.diagonal d *
        (((signedTranspositionSU a b h)⁻¹ :
            Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) =
      Matrix.diagonal (d ∘ transposition a b) := by
  rw [coe_signedTranspositionSU, coe_signedTranspositionSU_inv]
  exact signed_conj_diagonal a b d

end SignedWeylTransposition
end GUT
