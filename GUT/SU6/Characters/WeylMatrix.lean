import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# A concrete signed Weyl representative for the flipped `(3 6)` action

The ordinary permutation matrix for the transposition `(3 6)` has determinant
`-1`.  Multiplying by one diagonal sign gives a determinant-one signed
permutation matrix.  Its conjugation action on diagonal torus coordinates is
still the pure coordinate swap, because the signs cancel on diagonal matrices.
-/

namespace GUT
namespace WeylMatrix

open Matrix

abbrev I6 := Fin 6

def i3 : I6 := 2

def i6 : I6 := 5

def swap36 : Equiv.Perm I6 :=
  Equiv.swap i3 i6

theorem swap36_symm : swap36.symm = swap36 := by
  simp [swap36]

def sign36 (i : I6) : ℂ :=
  if i = i3 then -1 else 1

def sign36Matrix : Matrix I6 I6 ℂ :=
  Matrix.diagonal sign36

def permutation36Matrix : Matrix I6 I6 ℂ :=
  swap36.permMatrix ℂ

def signedSwap36Matrix : Matrix I6 I6 ℂ :=
  sign36Matrix * permutation36Matrix

def signedSwap36MatrixInv : Matrix I6 I6 ℂ :=
  permutation36Matrix * sign36Matrix

theorem sign36_sq (i : I6) : sign36 i * sign36 i = 1 := by
  by_cases h : i = i3 <;> simp [sign36, h]

theorem star_sign36 (i : I6) : star (sign36 i) = sign36 i := by
  by_cases h : i = i3 <;> simp [sign36, h]

theorem sign36Matrix_mul_self : sign36Matrix * sign36Matrix = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [sign36Matrix, sign36_sq]
  · simp [sign36Matrix, h]

theorem permutation36Matrix_mul_self : permutation36Matrix * permutation36Matrix = 1 := by
  change swap36.permMatrix ℂ * swap36.permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul (R := ℂ) swap36 swap36]
  simp [swap36]

theorem signedSwap36Matrix_mul_inv : signedSwap36Matrix * signedSwap36MatrixInv = 1 := by
  rw [signedSwap36Matrix, signedSwap36MatrixInv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc permutation36Matrix permutation36Matrix sign36Matrix]
  rw [← Matrix.mul_assoc sign36Matrix (permutation36Matrix * permutation36Matrix) sign36Matrix]
  rw [permutation36Matrix_mul_self]
  simp [sign36Matrix_mul_self]

theorem signedSwap36Matrix_inv_mul : signedSwap36MatrixInv * signedSwap36Matrix = 1 := by
  rw [signedSwap36Matrix, signedSwap36MatrixInv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sign36Matrix sign36Matrix permutation36Matrix]
  rw [← Matrix.mul_assoc permutation36Matrix (sign36Matrix * sign36Matrix) permutation36Matrix]
  rw [sign36Matrix_mul_self]
  simp [permutation36Matrix_mul_self]

theorem det_sign36Matrix : Matrix.det sign36Matrix = -1 := by
  rw [sign36Matrix, Matrix.det_diagonal]
  simp [Fin.prod_univ_six, sign36, i3]

theorem det_permutation36Matrix : Matrix.det permutation36Matrix = -1 := by
  rw [permutation36Matrix, Matrix.det_permutation]
  have h : i3 ≠ i6 := by decide
  rw [swap36, Equiv.Perm.sign_swap h]
  norm_num

theorem det_signedSwap36Matrix : Matrix.det signedSwap36Matrix = 1 := by
  rw [signedSwap36Matrix, Matrix.det_mul, det_sign36Matrix, det_permutation36Matrix]
  norm_num

theorem permutation36_conj_diagonal (d : I6 → ℂ) :
    permutation36Matrix * Matrix.diagonal d * permutation36Matrix =
      Matrix.diagonal (d ∘ swap36) := by
  rw [permutation36Matrix]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.submatrix, Matrix.diagonal, swap36_symm]
  · have hswap : swap36 i ≠ swap36.symm j := by
      rw [swap36_symm]
      exact fun hs => h (swap36.injective hs)
    simp [Matrix.submatrix, Matrix.diagonal, h, hswap]

theorem sign36Matrix_conj_diagonal (d : I6 → ℂ) :
    sign36Matrix * Matrix.diagonal d * sign36Matrix = Matrix.diagonal d := by
  rw [sign36Matrix, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [sign36_sq, mul_comm, mul_left_comm]
  · simp [h]

theorem signedSwap36_conj_diagonal (d : I6 → ℂ) :
    signedSwap36Matrix * Matrix.diagonal d * signedSwap36MatrixInv =
      Matrix.diagonal (d ∘ swap36) := by
  calc
    signedSwap36Matrix * Matrix.diagonal d * signedSwap36MatrixInv =
        sign36Matrix * (permutation36Matrix * Matrix.diagonal d * permutation36Matrix) *
          sign36Matrix := by
      simp only [signedSwap36Matrix, signedSwap36MatrixInv]
      noncomm_ring
    _ = sign36Matrix * Matrix.diagonal (d ∘ swap36) * sign36Matrix := by
      rw [permutation36_conj_diagonal]
    _ = Matrix.diagonal (d ∘ swap36) := sign36Matrix_conj_diagonal (d ∘ swap36)

theorem star_sign36Matrix : star sign36Matrix = sign36Matrix := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [sign36Matrix, star_sign36]
  · simp [sign36Matrix, h, Ne.symm h]

theorem star_permutation36Matrix : star permutation36Matrix = permutation36Matrix := by
  rw [permutation36Matrix, star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  simp [swap36]

theorem star_signedSwap36Matrix : star signedSwap36Matrix = signedSwap36MatrixInv := by
  rw [signedSwap36Matrix, signedSwap36MatrixInv, star_mul, star_sign36Matrix,
    star_permutation36Matrix]

theorem signedSwap36_mem_specialUnitary :
    signedSwap36Matrix ∈ Matrix.specialUnitaryGroup I6 ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    rw [star_signedSwap36Matrix]
    exact signedSwap36Matrix_mul_inv
  · exact det_signedSwap36Matrix

def signedSwap36SU : Matrix.specialUnitaryGroup I6 ℂ :=
  ⟨signedSwap36Matrix, signedSwap36_mem_specialUnitary⟩

theorem coe_signedSwap36SU :
    ((signedSwap36SU : Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) =
      signedSwap36Matrix :=
  rfl

theorem coe_signedSwap36SU_inv :
    ((signedSwap36SU⁻¹ : Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) =
      signedSwap36MatrixInv := by
  change star signedSwap36Matrix = signedSwap36MatrixInv
  exact star_signedSwap36Matrix

theorem signedSwap36SU_conj_diagonal (d : I6 → ℂ) :
    ((signedSwap36SU : Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) *
        Matrix.diagonal d *
        ((signedSwap36SU⁻¹ : Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) =
      Matrix.diagonal (d ∘ swap36) := by
  rw [coe_signedSwap36SU, coe_signedSwap36SU_inv]
  exact signedSwap36_conj_diagonal d

theorem signedSwap36SU_conj_diagonal_entry (d : I6 → ℂ) (i : I6) :
    (((signedSwap36SU : Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ) *
          Matrix.diagonal d *
          ((signedSwap36SU⁻¹ : Matrix.specialUnitaryGroup I6 ℂ) : Matrix I6 I6 ℂ)) i i =
      d (swap36 i) := by
  rw [signedSwap36SU_conj_diagonal]
  simp

end WeylMatrix
end GUT
