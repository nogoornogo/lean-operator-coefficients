import Math.LieGroups.E6.Minuscule.MatrixNormalizer
import Math.LieGroups.Matrix.MatrixLieGroupNormalizer

/-!
# Closed compact normalizer and its exact matrix-exponential criterion

This is an actual subgroup of SU(27), not a definition of the compact E6
group. Its components, global form and manifold tangent comparison remain
separate obligations.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The full SU(27) normalizer of the concrete 78-dimensional real form. -/
abbrev compactNormalizer : Subgroup (Matrix.specialUnitaryGroup (Fin 27) ℂ) :=
  MatrixLieGroupNormalizer.subgroup compactMatrixLieAlgebra

theorem compactNormalizer_isClosed :
    IsClosed (compactNormalizer : Set (Matrix.specialUnitaryGroup (Fin 27) ℂ)) :=
  MatrixLieGroupNormalizer.isClosed_subgroup compactMatrixLieAlgebra

theorem compactNormalizer_isCompact :
    IsCompact (compactNormalizer : Set (Matrix.specialUnitaryGroup (Fin 27) ℂ)) :=
  compactNormalizer_isClosed.isCompact

/-- Actual matrix image of the subgroup. -/
abbrev compactNormalizerMatrices : Submonoid Matrix27 :=
  MatrixLieGroupNormalizer.matrixCarrier compactMatrixLieAlgebra

/-- No additional skew-Hermitian trace-zero exponential directions occur. -/
theorem mem_compactMatrix_iff_exp_mem_normalizer (X : Matrix27) :
    X ∈ compactMatrixLieAlgebra ↔
      ∀ t : ℝ, exp (t • X) ∈ compactNormalizerMatrices :=
  (compactMatrix_mem_iff_normalizes_skew_trace_zero X).trans
    (MatrixLieGroupNormalizer.exp_mem_matrixCarrier_iff compactMatrixLieAlgebra X).symm

theorem exp_compactMatrix_mem_normalizer (X : Matrix27) (hX : X ∈ compactMatrixLieAlgebra)
    (t : ℝ) : exp (t • X) ∈ compactNormalizerMatrices :=
  (mem_compactMatrix_iff_exp_mem_normalizer X).mp hX t

/-- The earlier real form embeds into the constructed group's exponential directions. -/
theorem exp_compactRealForm_mem_normalizer (X : compactRealForm) (t : ℝ) :
    exp (t • X.val.val) ∈ compactNormalizerMatrices :=
  exp_compactMatrix_mem_normalizer _ ⟨X, rfl⟩ t

theorem exp_generator_mem_normalizer (k : Fin 3) (i : Fin 6) (t : ℝ) :
    exp (t • (compactGeneratorElement k i).val.val) ∈ compactNormalizerMatrices :=
  exp_compactRealForm_mem_normalizer _ t

end

end Math.E6.Minuscule
