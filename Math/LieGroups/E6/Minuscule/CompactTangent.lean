import Math.LieGroups.E6.Minuscule.CompactLieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Actual tangent image of the compact candidate

The differential of the matrix inclusion at one has precisely the
previously constructed real form as image. Bracket compatibility is a
separate obligation, not inferred from this linear identification.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

theorem compactMatrix_writtenInExtChartAt_one :
    writtenInExtChartAt 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27)
      (1 : compactIdentityComponent) compactMatrix =
      fun X : compactMatrixLieAlgebra => exp (X : Matrix27) := by
  funext X
  simp only [writtenInExtChartAt, Function.comp_def, ext_chart_model_space_apply,
    compact_extChartAt_symm_apply, one_mul, compactMatrix, compactExp_coe]

/-- Coordinate-independent tangent map, with the standard tangent/model casts explicit. -/
def compactTangentInclusion :
    TangentSpace 𝓘(ℝ, compactMatrixLieAlgebra) (1 : compactIdentityComponent) →L[ℝ]
      TangentSpace 𝓘(ℝ, Matrix27) (compactMatrix 1) :=
  (tangentSpaceCastModel 𝓘(ℝ, Matrix27) (compactMatrix 1)).symm.toContinuousLinearMap ∘L
    compactMatrixLieAlgebra.toSubmodule.subtypeL ∘L
      (tangentSpaceCastModel 𝓘(ℝ, compactMatrixLieAlgebra)
        (1 : compactIdentityComponent)).toContinuousLinearMap

theorem mfderiv_compactMatrix_one :
    mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1 =
      compactTangentInclusion := by
  have hd := (contMDiff_compactMatrix.mdifferentiable (by simp)).mdifferentiableAt
    (x := (1 : compactIdentityComponent))
  have he : fderiv ℝ (fun X : compactMatrixLieAlgebra => exp (X : Matrix27)) 0 =
      compactMatrixLieAlgebra.toSubmodule.subtypeL := by
    have h := compactExp_hasStrictFDerivAt_zero.hasFDerivAt.fderiv
    simpa only [compactExp_coe] using h
  simp only [mfderiv, hd, ite_eq_left, compactMatrix_writtenInExtChartAt_one,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    compact_extChartAt_apply, inv_mul_cancel, compactChartLog_one, he,
    compactTangentInclusion]

def compactTangentEquiv :
    TangentSpace 𝓘(ℝ, compactMatrixLieAlgebra) (1 : compactIdentityComponent) ≃L[ℝ]
      compactMatrixLieAlgebra :=
  tangentSpaceCastModel 𝓘(ℝ, compactMatrixLieAlgebra) (1 : compactIdentityComponent)

theorem compactTangent_matrix (v :
    TangentSpace 𝓘(ℝ, compactMatrixLieAlgebra) (1 : compactIdentityComponent)) :
    tangentSpaceCastModel 𝓘(ℝ, Matrix27) (compactMatrix 1)
      (mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1 v) =
      (compactTangentEquiv v : Matrix27) := by
  rw [mfderiv_compactMatrix_one]
  simp only [compactTangentInclusion, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem mfderiv_compactMatrix_one_injective : Function.Injective
    (mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1) := by
  intro v w hvw
  apply compactTangentEquiv.injective
  apply Subtype.ext
  simpa only [compactTangent_matrix] using
    congrArg (tangentSpaceCastModel 𝓘(ℝ, Matrix27) (compactMatrix 1)) hvw

theorem exists_tangent_matrix_iff (A : Matrix27) :
    (∃ v, tangentSpaceCastModel 𝓘(ℝ, Matrix27) (compactMatrix 1)
      (mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactMatrix 1 v) = A) ↔
      A ∈ compactMatrixLieAlgebra := by
  simp only [compactTangent_matrix]
  constructor
  · rintro ⟨v, rfl⟩
    exact (compactTangentEquiv v).property
  · intro hA
    exact ⟨compactTangentEquiv.symm ⟨A, hA⟩, by simp⟩

end

end Math.E6.Minuscule
