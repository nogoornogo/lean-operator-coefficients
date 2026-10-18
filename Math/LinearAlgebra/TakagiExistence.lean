import Math.LinearAlgebra.AntilinearSpectral
import Math.LinearAlgebra.UnitaryCongruenceCertificate

/-! Takagi existence for every finite complex symmetric matrix. -/
namespace Math.TakagiExistence
set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped ComplexConjugate
variable {I : Type*} [Fintype I] [DecidableEq I]

def anti (M : Matrix I I ℂ) (x : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  toLp 2 (fun i => conj (M.mulVec x i))

omit [DecidableEq I] in
theorem anti_add (M : Matrix I I ℂ) (x y : EuclideanSpace ℂ I) :
    anti M (x + y) = anti M x + anti M y := by
  ext i
  simp [anti, Matrix.mulVec_add]

omit [DecidableEq I] in
theorem anti_smul (M : Matrix I I ℂ) (z : ℂ) (x : EuclideanSpace ℂ I) :
    anti M (z • x) = conj z • anti M x := by
  ext i
  simp [anti, Matrix.mulVec_smul, smul_eq_mul]

omit [DecidableEq I] in
theorem inner_anti (M : Matrix I I ℂ) (x y : EuclideanSpace ℂ I) :
    inner ℂ (anti M x) y = (M.mulVec x) ⬝ᵥ y := by
  simp [PiLp.inner_apply, anti, dotProduct, RCLike.inner_apply, mul_comm]

omit [DecidableEq I] in
theorem anti_symmetric (M : Matrix I I ℂ) (hM : M.IsSymm)
    (x y : EuclideanSpace ℂ I) : inner ℂ (anti M x) y = inner ℂ (anti M y) x := by
  rw [inner_anti, inner_anti, dotProduct_comm, ← dotProduct_transpose_mulVec, hM]
  exact dotProduct_comm _ _

theorem exists_real_diagonal (M : Matrix I I ℂ) (hM : M.IsSymm) :
    ∃ (r : I → ℝ) (U : unitaryGroup I ℂ),
      UnitaryCongruenceCertificate.Congruent M (diagonal (fun i => (r i : ℂ))) U := by
  obtain ⟨b₀, r₀, hb₀⟩ := AntilinearSpectral.exists_basis (Fintype.card I)
    (finrank_euclideanSpace) (anti M) (anti_add M) (anti_smul M)
      (anti_symmetric M hM)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let b := b₀.reindex e
  let r : I → ℝ := r₀ ∘ e.symm
  have hb (i : I) : anti M (b i) = (r i : ℂ) • b i := by
    simpa [b, r] using hb₀ (e.symm i)
  let A : Matrix I I ℂ := fun i j => b j i
  have hA : A ∈ unitaryGroup I ℂ := by
    rw [mem_unitaryGroup_iff']
    ext i j
    change (A.conjTranspose * A) i j = _
    rw [← inner_matrix_col_col]
    change inner ℂ (b i) (b j) = _
    simpa [Matrix.one_apply] using orthonormal_iff_ite.mp b.orthonormal i j
  refine ⟨r, ⟨A, hA⟩, ?_⟩
  change A.transpose * M * A = diagonal (fun i => (r i : ℂ))
  ext i j
  have hij := congrArg (fun x : EuclideanSpace ℂ I => inner ℂ x (b i)) (hb j)
  rw [inner_anti, inner_smul_left] at hij
  rw [dotProduct_comm] at hij
  change (b i : I → ℂ) ⬝ᵥ (M.mulVec (b j)) = _ at hij
  rw [orthonormal_iff_ite.mp b.orthonormal] at hij
  simp only [Complex.conj_ofReal] at hij
  rw [Matrix.mul_assoc]
  change (b i : I → ℂ) ⬝ᵥ (M.mulVec (b j)) = _
  by_cases he : i = j
  · subst j; simpa [diagonal_apply] using hij
  · simpa [diagonal_apply, he, Ne.symm he] using hij

theorem exists_nonnegative_diagonal (M : Matrix I I ℂ) (hM : M.IsSymm) :
    ∃ (m : I → ℝ), (∀ i, 0 ≤ m i) ∧ ∃ U : unitaryGroup I ℂ,
      UnitaryCongruenceCertificate.Congruent M (diagonal (fun i => (m i : ℂ))) U := by
  obtain ⟨r, U, hU⟩ := exists_real_diagonal M hM
  let c : I → ℂ := fun i => (r i : ℂ)
  refine ⟨fun i => ‖c i‖, fun i => norm_nonneg _,
    U * MajoranaPhaseNormalization.diagonalPhase (MajoranaPhaseNormalization.phase c), ?_⟩
  exact UnitaryCongruenceCertificate.comp hU (MajoranaPhaseNormalization.diagonalPhase_spec c)

theorem symmetric_iff_exists_nonnegative_diagonal (M : Matrix I I ℂ) :
    M.IsSymm ↔ ∃ (m : I → ℝ), (∀ i, 0 ≤ m i) ∧ ∃ U : unitaryGroup I ℂ,
      UnitaryCongruenceCertificate.Congruent M (diagonal (fun i => (m i : ℂ))) U := by
  constructor
  · exact exists_nonnegative_diagonal M
  · rintro ⟨m, _, U, hU⟩
    have hi := UnitaryCongruenceCertificate.inverse hU
    change (U⁻¹).val.transpose * diagonal (fun i => (m i : ℂ)) * (U⁻¹).val = M at hi
    change M.transpose = M
    rw [← hi]
    simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

/-- A nondiagonal singular symmetric matrix is covered without a rank hypothesis. -/
theorem singular_nondiagonal_control :
    ∃ (m : Fin 2 → ℝ), (∀ i, 0 ≤ m i) ∧ ∃ U : unitaryGroup (Fin 2) ℂ,
      UnitaryCongruenceCertificate.Congruent (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℂ)
        (diagonal (fun i => (m i : ℂ))) U := by
  apply exists_nonnegative_diagonal
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Symmetry is necessary; this is not a theorem for arbitrary complex matrices. -/
theorem nonsymmetric_control :
    ¬ ∃ (m : Fin 2 → ℝ), (∀ i, 0 ≤ m i) ∧ ∃ U : unitaryGroup (Fin 2) ℂ,
      UnitaryCongruenceCertificate.Congruent (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        (diagonal (fun i => (m i : ℂ))) U := by
  rw [← symmetric_iff_exists_nonnegative_diagonal]
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
  norm_num [Matrix.transpose_apply] at hh

end
end Math.TakagiExistence
