import Math.LieGroups.Symplectic.CompactGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The standard diagonal torus of USp(2n) and its actual inversion element.
Maximality and conjugacy of arbitrary elements to this torus are not assumed
or asserted here. -/

set_option autoImplicit false

namespace Math.CompactSymplectic

noncomputable section

abbrev Torus (n : ℕ) := Fin n → Circle

def torusMatrix {n : ℕ} (z : Torus n) : Mat n :=
  Matrix.fromBlocks (Matrix.diagonal fun i => (z i : ℂ)) 0 0
    (Matrix.diagonal fun i => ((z i)⁻¹ : Circle))

private theorem diagonal_unitary {n : ℕ} (z : Torus n) :
    Matrix.diagonal (fun i => (z i : ℂ)) *
      (Matrix.diagonal fun i => (z i : ℂ)).conjTranspose = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h (i : Fin n) : (z i : ℂ) * star (z i : ℂ) = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
    simp
  change Matrix.diagonal (fun i => (z i : ℂ) * star (z i : ℂ)) = 1
  rw [funext h]
  exact Matrix.diagonal_one

theorem torusMatrix_unitary {n : ℕ} (z : Torus n) :
    torusMatrix z ∈ Matrix.unitaryGroup (Index n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [torusMatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    diagonal_unitary, Matrix.fromBlocks_one]

theorem torusMatrix_symplectic {n : ℕ} (z : Torus n) :
    torusMatrix z ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  rw [torusMatrix, SymplecticGroup.fromBlocks_mem_iff]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.transpose_zero,
    Matrix.diagonal_transpose, sub_zero, true_and]
  rw [Matrix.diagonal_mul_diagonal]
  have h (i : Fin n) : (z i : ℂ) * ((z i)⁻¹ : Circle) = 1 := by
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  change Matrix.diagonal (fun i => (z i : ℂ) * ((z i)⁻¹ : Circle)) = 1
  rw [funext h]
  exact Matrix.diagonal_one

def torusHom (n : ℕ) : Torus n →* Group n where
  toFun z := ⟨⟨torusMatrix z, torusMatrix_unitary z⟩, torusMatrix_symplectic z⟩
  map_one' := by
    apply matrix_injective n
    simp [matrix, torusMatrix, Matrix.fromBlocks_one]
  map_mul' z w := by
    apply matrix_injective n
    simp [matrix, torusMatrix, Matrix.diagonal_mul_diagonal, mul_comm]

@[simp] theorem matrix_torusHom {n : ℕ} (z : Torus n) : matrix (torusHom n z) = torusMatrix z := rfl

theorem torusHom_injective (n : ℕ) : Function.Injective (torusHom n) := by
  intro z w he
  funext i
  apply Circle.coe_injective
  have hh := congrArg (fun g : Group n => matrix g (.inl i) (.inl i)) he
  simpa [torusMatrix] using hh

theorem torusHom_continuous (n : ℕ) : Continuous (torusHom n) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (torusMatrix (n := n))
  unfold torusMatrix
  fun_prop

theorem J_unitary (n : ℕ) : Matrix.J (Fin n) ℂ ∈ Matrix.unitaryGroup (Index n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp [Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_one]

def inversionElement (n : ℕ) : Group n :=
  ⟨⟨Matrix.J (Fin n) ℂ, J_unitary n⟩, SymplecticGroup.J_mem (Fin n) ℂ⟩

@[simp] theorem matrix_inversionElement (n : ℕ) :
    matrix (inversionElement n) = Matrix.J (Fin n) ℂ := rfl

theorem torusHom_inversion_commute {n : ℕ} (z : Torus n) :
    torusHom n z⁻¹ * inversionElement n = inversionElement n * torusHom n z := by
  apply matrix_injective n
  change torusMatrix z⁻¹ * Matrix.J (Fin n) ℂ = Matrix.J (Fin n) ℂ * torusMatrix z
  simp only [torusMatrix, Matrix.J, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul,
    add_zero, zero_add, neg_zero, Pi.inv_apply, inv_inv]

theorem torusHom_inverse_conjugate {n : ℕ} (z : Torus n) :
    torusHom n z⁻¹ = inversionElement n * torusHom n z * (inversionElement n)⁻¹ := by
  rw [← torusHom_inversion_commute, mul_inv_cancel_right]

end

end Math.CompactSymplectic
