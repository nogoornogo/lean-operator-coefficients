import Math.LieGroups.Symplectic.Torus

/-! The actual continuous embedding U(n) -> USp(2n), A |-> diag(A, conj A),
and its restriction to SU(n). -/

set_option autoImplicit false

namespace Math.CompactSymplectic

noncomputable section

def unitaryMatrix {n : ℕ} (g : Matrix.unitaryGroup (Fin n) ℂ) : Mat n :=
  Matrix.fromBlocks g.val 0 0 (g.val.map star)

theorem unitaryMatrix_unitary {n : ℕ} (g : Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryMatrix g ∈ Matrix.unitaryGroup (Index n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have h₁ : g.val * g.val.conjTranspose = 1 := g.property.2
  have h₂ : g.val.map star * (g.val.map star).conjTranspose = 1 :=
    (Matrix.UnitaryGroup.map_star g).property.2
  simp only [unitaryMatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    h₁, h₂, Matrix.fromBlocks_one]

theorem unitaryMatrix_symplectic {n : ℕ} (g : Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryMatrix g ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  rw [unitaryMatrix, SymplecticGroup.fromBlocks_mem_iff]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.transpose_zero, sub_zero, true_and]
  have hh : g.val.conjTranspose * g.val = 1 := g.property.1
  have ht := congrArg Matrix.transpose hh
  simpa only [Matrix.transpose_mul, Matrix.conjTranspose_transpose, Matrix.transpose_one]
    using ht

def unitaryInclusion (n : ℕ) : Matrix.unitaryGroup (Fin n) ℂ →* Group n where
  toFun g := ⟨⟨unitaryMatrix g, unitaryMatrix_unitary g⟩, unitaryMatrix_symplectic g⟩
  map_one' := by
    apply matrix_injective n
    simp [matrix, unitaryMatrix, Matrix.fromBlocks_one]
  map_mul' g h := by
    apply matrix_injective n
    change unitaryMatrix (g * h) = unitaryMatrix g * unitaryMatrix h
    simp only [unitaryMatrix, Matrix.UnitaryGroup.mul_val, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 1
    exact Matrix.map_mul (f := starRingEnd ℂ)

@[simp] theorem matrix_unitaryInclusion {n : ℕ} (g : Matrix.unitaryGroup (Fin n) ℂ) :
    matrix (unitaryInclusion n g) = unitaryMatrix g := rfl

theorem unitaryInclusion_injective (n : ℕ) : Function.Injective (unitaryInclusion n) := by
  intro g h he
  apply Subtype.ext
  ext i j
  exact congrArg (fun u : Group n => matrix u (.inl i) (.inl j)) he

theorem unitaryInclusion_continuous (n : ℕ) : Continuous (unitaryInclusion n) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (unitaryMatrix (n := n))
  unfold unitaryMatrix
  fun_prop

def specialUnitaryInclusion (n : ℕ) : Matrix.specialUnitaryGroup (Fin n) ℂ →* Group n :=
  (unitaryInclusion n).comp (Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup)

theorem specialUnitaryInclusion_injective (n : ℕ) :
    Function.Injective (specialUnitaryInclusion n) := by
  intro g h he
  exact Subtype.ext (congrArg (fun A : Matrix.unitaryGroup (Fin n) ℂ => A.val)
    (unitaryInclusion_injective n he))

theorem specialUnitaryInclusion_continuous (n : ℕ) :
    Continuous (specialUnitaryInclusion n) :=
  (unitaryInclusion_continuous n).comp (continuous_induced_rng.mpr continuous_subtype_val)

theorem specialUnitaryInclusion_diagonal {n : ℕ}
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) (z : Torus n)
    (hg : g.val = Matrix.diagonal (fun i => (z i : ℂ))) :
    specialUnitaryInclusion n g = torusHom n z := by
  apply matrix_injective n
  change Matrix.fromBlocks g.val 0 0 (g.val.map star) = torusMatrix z
  rw [hg]
  simp only [torusMatrix, Matrix.diagonal_map, star_zero]
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  rw [Complex.star_def, Circle.coe_inv_eq_conj]

end

end Math.CompactSymplectic
