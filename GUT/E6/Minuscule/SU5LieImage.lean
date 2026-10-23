import GUT.E6.Minuscule.SU5Exponential
import Math.LieGroups.E6.Minuscule.CompactIdentityComponent

open Math

/-! A finite basis calculation places every compact SU(5) direction in
the actual E6 real matrix algebra. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GUT.E6.Minuscule.SU5Coordinates

open Math.E6.Minuscule Math.E6
open SparseMatrixCertificate LieData
open scoped Matrix Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

def elementaryInt (i j : Fin 5) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.single i j 1 - if i = j then Matrix.single 4 4 1 else 0

/-- Coefficients in the already kernel-checked E6 basis, not new Lie generators. -/
def elementaryCoefficients : Fin 5 → Fin 5 → List (Fin 78 × ℤ) :=
  ![![[(17, 1), (16, 1), (15, 1), (14, 1)], [(5, 1)], [(22, 1)], [(32, 1)], [(42, 1)]],
    ![[(11, 1)], [(16, 1), (15, 1), (14, 1)], [(4, 1)], [(21, 1)], [(31, 1)]],
    ![[(27, -1)], [(10, 1)], [(15, 1), (14, 1)], [(3, 1)], [(20, 1)]],
    ![[(37, 1)], [(26, -1)], [(9, 1)], [(14, 1)], [(2, 1)]],
    ![[(47, -1)], [(36, 1)], [(25, -1)], [(8, 1)], []]]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem elementary_comparison (i j : Fin 5) (a b : Index) :
    sign a * eval (combination e6Basis (elementaryCoefficients i j))
      (coordinate a) (coordinate b) * sign b = blockMatrix (elementaryInt i j) a b := by
  fin_cases i <;> fin_cases j <;>
    revert a b <;>
    dsimp only [blockMatrix, wedgeMatrix, elementaryInt] <;>
    decide +kernel

noncomputable section

def blockLinear : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix Index Index ℂ where
  toFun := blockMatrix
  map_add' X Y := by
    ext a b
    rcases a with a | a | ⟨k, a⟩ | a <;> rcases b with b | b | ⟨l, b⟩ | b <;>
      simp only [blockMatrix, wedgeMatrix, Matrix.add_apply] <;> (try split_ifs) <;> ring
  map_smul' z X := by
    ext a b
    rcases a with a | a | ⟨k, a⟩ | a <;> rcases b with b | b | ⟨l, b⟩ | b <;>
      simp only [blockMatrix, wedgeMatrix, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      (try split_ifs) <;> ring

def ambientLinear : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix27 :=
  matrixCoordinates.symm.toLinearMap.comp blockLinear

theorem elementary_image (i j : Fin 5) :
    ambientInfinitesimal ((elementaryInt i j).map (Int.castRingHom ℂ)) =
      realize ℂ (combination e6Basis (elementaryCoefficients i j)) := by
  apply matrixCoordinates.injective
  change matrixCoordinates (matrixCoordinates.symm _) = _
  rw [matrixCoordinates.apply_symm_apply]
  ext a b
  rw [matrixCoordinates_apply, blockMatrix_map]
  simpa only [realize, Matrix.map_apply, Int.coe_castRingHom, Int.cast_mul] using
    congrArg (fun z : ℤ => (z : ℂ)) (elementary_comparison i j a b).symm

theorem elementary_image_mem (i j : Fin 5) :
    ambientInfinitesimal ((elementaryInt i j).map (Int.castRingHom ℂ)) ∈ matrixLieAlgebra ℂ := by
  rw [elementary_image]
  apply realize_combination_mem
  intro k
  rw [← matrixLieAlgebra_span]
  exact Submodule.subset_span (Set.mem_range_self k)

theorem traceless_decomposition (X : Matrix (Fin 5) (Fin 5) ℂ) (hX : Matrix.trace X = 0) :
    X = ∑ i : Fin 5, ∑ j : Fin 5, X i j • (elementaryInt i j).map (Int.castRingHom ℂ) := by
  have ht : X 0 0 + X 1 1 + X 2 2 + X 3 3 + X 4 4 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using hX
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_succ, elementaryInt, Matrix.map_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination ht

theorem ambientInfinitesimal_mem (X : Matrix (Fin 5) (Fin 5) ℂ) (hX : Matrix.trace X = 0) :
    ambientInfinitesimal X ∈ matrixLieAlgebra ℂ := by
  change ambientLinear X ∈ matrixLieAlgebra ℂ
  rw [traceless_decomposition X hX, map_sum]
  apply (matrixLieAlgebra ℂ).toSubmodule.sum_mem
  intro i _
  rw [map_sum]
  apply (matrixLieAlgebra ℂ).toSubmodule.sum_mem
  intro j _
  rw [map_smul]
  exact (matrixLieAlgebra ℂ).smul_mem _ (elementary_image_mem i j)

private theorem wedgeMatrix_adjoint (X : Matrix (Fin 5) (Fin 5) ℂ) :
    wedgeMatrix Xᴴ = (wedgeMatrix X)ᴴ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [wedgeMatrix, Matrix.conjTranspose_apply]

theorem blockMatrix_adjoint (X : Matrix (Fin 5) (Fin 5) ℂ) :
    blockMatrix Xᴴ = (blockMatrix X)ᴴ := by
  ext a b
  rcases a with a | a | ⟨k, a⟩ | a <;> rcases b with b | b | ⟨l, b⟩ | b <;>
    simp only [Matrix.conjTranspose_apply, blockMatrix, star_zero]
  · by_cases h : k = l
    · subst l
      simp
    · simp [h, Ne.symm h]
  · exact congrFun (congrFun (wedgeMatrix_adjoint X) a) b

theorem ambientInfinitesimal_skew (X : Matrix (Fin 5) (Fin 5) ℂ) (hX : Xᴴ = -X) :
    (ambientInfinitesimal X)ᴴ = -ambientInfinitesimal X := by
  apply matrixCoordinates.injective
  rw [matrixCoordinates_adjoint, map_neg]
  change (matrixCoordinates (matrixCoordinates.symm (blockMatrix X)))ᴴ =
    -(matrixCoordinates (matrixCoordinates.symm (blockMatrix X)))
  rw [matrixCoordinates.apply_symm_apply, ← blockMatrix_adjoint, hX]
  change blockLinear (-X) = -blockLinear X
  exact map_neg blockLinear X

theorem ambientInfinitesimal_compact (X : SpecialUnitaryLieAlgebra.CompactRealForm (Fin 5)) :
    ambientInfinitesimal (X : Matrix (Fin 5) (Fin 5) ℂ) ∈ compactMatrixLieAlgebra := by
  apply (mem_compactMatrixLieAlgebra _).mpr
  refine ⟨ambientInfinitesimal_mem _ X.toSpecialLinear.property,
    ambientInfinitesimal_skew _ ?_⟩
  exact X.skewAdjoint

end

end GUT.E6.Minuscule.SU5Coordinates
