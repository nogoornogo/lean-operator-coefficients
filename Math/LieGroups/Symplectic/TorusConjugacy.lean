import Math.LieGroups.Symplectic.PairedEigenbasis

/-! Actual symplectic, not merely unitary, diagonalization. -/

set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace Math.CompactSymplectic

noncomputable section

def basisMatrix {n : ℕ} (b : OrthonormalBasis (Index n) ℂ (Hilbert n)) : Mat n :=
  (EuclideanSpace.basisFun (Index n) ℂ).toBasis.toMatrix b

@[simp] theorem basisMatrix_apply {n : ℕ} (b : OrthonormalBasis (Index n) ℂ (Hilbert n))
    (i j : Index n) : basisMatrix b i j = b j i := rfl

theorem basisMatrix_unitary {n : ℕ} (b : OrthonormalBasis (Index n) ℂ (Hilbert n)) :
    basisMatrix b ∈ Matrix.unitaryGroup (Index n) ℂ :=
  (EuclideanSpace.basisFun (Index n) ℂ).toMatrix_orthonormalBasis_mem_unitary b

theorem mul_J_left_column {n : ℕ} (A : Mat n) (i : Index n) (j : Fin n) :
    (A * Matrix.J (Fin n) ℂ) i (.inl j) = A i (.inr j) := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_J_right_column {n : ℕ} (A : Mat n) (i : Index n) (j : Fin n) :
    (A * Matrix.J (Fin n) ℂ) i (.inr j) = -A i (.inl j) := by
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Matrix.one_apply]

theorem J_mul_map_star_column {n : ℕ} (A : Mat n) (j : Index n) :
    (fun i => (Matrix.J (Fin n) ℂ * A.map star) i j) =
      quaternionicMap n (fun i => A i j) := by
  rw [quaternionicMap_matrix]
  rfl

theorem symplectic_of_unitary_mul_J {n : ℕ} {A : Mat n}
    (hu : A ∈ Matrix.unitaryGroup (Index n) ℂ)
    (hq : A * Matrix.J (Fin n) ℂ = Matrix.J (Fin n) ℂ * A.map star) :
    A ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  rw [SymplecticGroup.mem_iff, hq, Matrix.mul_assoc]
  have ht : A.map star * A.transpose = 1 := by
    have hh : A * A.conjTranspose = 1 := hu.2
    simpa only [Matrix.transpose_mul, Matrix.conjTranspose_transpose, Matrix.transpose_one]
      using congrArg Matrix.transpose hh
  rw [ht, Matrix.mul_one]

theorem basisMatrix_symplectic {n : ℕ} (b : OrthonormalBasis (Index n) ℂ (Hilbert n))
    (hq : ∀ i, WithLp.ofLp (b (.inr i)) = quaternionicMap n (WithLp.ofLp (b (.inl i)))) :
    basisMatrix b ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  apply symplectic_of_unitary_mul_J (basisMatrix_unitary b)
  ext i j
  have hr (j : Fin n) : quaternionicMap n (WithLp.ofLp (b (.inr j))) =
      -WithLp.ofLp (b (.inl j)) := by rw [hq, quaternionicMap_square]
  cases j with
  | inl j =>
    rw [mul_J_left_column]
    have hh := congrFun (J_mul_map_star_column (basisMatrix b) (.inl j)) i
    change _ = quaternionicMap n (WithLp.ofLp (b (.inl j))) i at hh
    rw [← hq] at hh
    exact hh.symm
  | inr j =>
    rw [mul_J_right_column]
    have hh := congrFun (J_mul_map_star_column (basisMatrix b) (.inr j)) i
    change _ = quaternionicMap n (WithLp.ofLp (b (.inr j))) i at hh
    rw [hr] at hh
    exact hh.symm

theorem exists_torus_conjugate {n : ℕ} (g : Group n) :
    ∃ (z : Torus n) (u : Group n), g = u * torusHom n z * u⁻¹ := by
  obtain ⟨b, z, hq, ht⟩ := exists_paired_eigenbasis g
  let u : Group n := ⟨⟨basisMatrix b, basisMatrix_unitary b⟩, basisMatrix_symplectic b hq⟩
  have hu : g * u = u * torusHom n z := by
    apply matrix_injective n
    change matrix g * basisMatrix b = basisMatrix b * torusMatrix z
    rw [torusMatrix, Matrix.fromBlocks_diagonal]
    ext i j
    rw [Matrix.mul_diagonal]
    change (matrix g *ᵥ WithLp.ofLp (b j)) i = _
    cases j with
    | inl j => simpa [smul_eq_mul, mul_comm] using congrFun (ht j) i
    | inr j =>
      have he : defining n g (WithLp.ofLp (b (.inl j))) =
          (z j : ℂ) • WithLp.ofLp (b (.inl j)) := ht j
      have hh := quaternionicMap_circle_eigen g he
      rw [← hq] at hh
      simpa [defining_apply, smul_eq_mul, mul_comm] using congrFun hh i
  refine ⟨z, u, ?_⟩
  rw [← hu, mul_inv_cancel_right]

theorem inverse_conjugate {n : ℕ} (g : Group n) :
    ∃ u : Group n, g⁻¹ = u * g * u⁻¹ := by
  obtain ⟨z, u, hg⟩ := exists_torus_conjugate g
  have ht : (torusHom n z)⁻¹ =
      inversionElement n * torusHom n z * (inversionElement n)⁻¹ := by
    rw [← map_inv]
    exact torusHom_inverse_conjugate z
  refine ⟨u * inversionElement n * u⁻¹, ?_⟩
  rw [hg]
  simp only [_root_.mul_inv_rev, inv_inv]
  rw [ht]
  group

end

end Math.CompactSymplectic
