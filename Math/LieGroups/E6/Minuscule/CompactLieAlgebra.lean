import Math.LieGroups.E6.Minuscule.CompactTangent
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Adjoint.Units.Basic

/-! # Tangent Lie algebra of the actual connected compact candidate -/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

def compactUnits : ContMDiffMonoidMorphism 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) ∞
    compactIdentityComponent Matrix27ˣ where
  toFun g :=
    { val := compactMatrix g
      inv := compactMatrix g⁻¹
      val_inv := by rw [← compactMatrix_mul, mul_inv_cancel, compactMatrix_one]
      inv_val := by rw [← compactMatrix_mul, inv_mul_cancel, compactMatrix_one] }
  map_one' := Units.ext compactMatrix_one
  map_mul' g h := Units.ext (compactMatrix_mul g h)
  contMDiff_toFun := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    exact contMDiff_compactMatrix

@[simp] theorem compactUnits_val (g : compactIdentityComponent) :
    (compactUnits g : Matrix27) = compactMatrix g := rfl

theorem compactUnits_injective : Function.Injective compactUnits :=
  fun _ _ h => compactMatrix_injective (congrArg Units.val h)

theorem compactUnits_writtenInExtChartAt_one :
    writtenInExtChartAt 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27)
      (1 : compactIdentityComponent) compactUnits =
      fun X : compactMatrixLieAlgebra => exp (X : Matrix27) := by
  funext X
  simp only [writtenInExtChartAt, Function.comp_def, extChartAt_coe,
    modelWithCornersSelf_coe, id_eq, Units.chartAt_apply,
    compact_extChartAt_symm_apply, one_mul, compactUnits_val, compactMatrix, compactExp_coe]

theorem compactUnits_mfderiv_one (v : GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra)
    compactIdentityComponent) :
    (show Matrix27 from mfderiv 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactUnits 1 v) =
      (compactTangentEquiv v : Matrix27) := by
  have hd : MDifferentiableAt 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) compactUnits 1 :=
    (compactUnits.contMDiff_toFun.mdifferentiable (by simp)).mdifferentiableAt
  have he : fderiv ℝ (fun X : compactMatrixLieAlgebra => exp (X : Matrix27)) 0 =
      compactMatrixLieAlgebra.toSubmodule.subtypeL := by
    simpa only [compactExp_coe] using compactExp_hasStrictFDerivAt_zero.hasFDerivAt.fderiv
  simp only [mfderiv, hd, ite_eq_left, compactUnits_writtenInExtChartAt_one,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    compact_extChartAt_apply, inv_mul_cancel, compactChartLog_one, he,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl

def compactTangentMatrixLieHom :
    GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent →ₗ⁅ℝ⁆ Matrix27 :=
  (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix27)).toLieHom.comp
    ((lieMap compactUnits).comp
      (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := 𝓘(ℝ, compactMatrixLieAlgebra)) (G := compactIdentityComponent)
        BoundarylessManifold.isInteriorPoint).symm.toLieHom)

theorem compactTangentMatrixLieHom_apply
    (v : GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent) :
    compactTangentMatrixLieHom v = (compactTangentEquiv v : Matrix27) := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := 𝓘(ℝ, compactMatrixLieAlgebra)) (G := compactIdentityComponent)
    BoundarylessManifold.isInteriorPoint
  have h := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap compactUnits (e.symm v)
  have hh := congrArg (fun z : GroupLieAlgebra 𝓘(ℝ, Matrix27) Matrix27ˣ => show Matrix27 from z) h
  simpa only [compactTangentMatrixLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    TauCeti.Lie.unitsLieAlgebraLieEquiv_apply, unitsLieAlgebraEquiv_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    LieEquiv.apply_symm_apply, compactUnits_mfderiv_one, e] using hh

/-- The geometric tangent bracket, transported through the actual differential. -/
def compactTangentLieEquiv :
    GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent ≃ₗ⁅ℝ⁆
      compactMatrixLieAlgebra :=
  { compactTangentEquiv.toLinearEquiv with
    map_lie' := by
      intro X Y
      apply Subtype.ext
      change (compactTangentEquiv ⁅X, Y⁆ : Matrix27) =
        ⁅(compactTangentEquiv X : Matrix27), (compactTangentEquiv Y : Matrix27)⁆
      simpa only [compactTangentMatrixLieHom_apply] using
        compactTangentMatrixLieHom.map_lie X Y }

@[simp] theorem compactTangentLieEquiv_apply
    (X : GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent) :
    compactTangentLieEquiv X = compactTangentEquiv X := rfl

/-- Explicit invariant-vector-field check guards against substituting the model-space bracket. -/
theorem compact_invariantVectorField_bracket
    (X Y : GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent) :
    (compactTangentEquiv (VectorField.mlieBracket 𝓘(ℝ, compactMatrixLieAlgebra)
      (mulInvariantVectorField X) (mulInvariantVectorField Y) 1) : Matrix27) =
      (compactTangentEquiv X : Matrix27) * (compactTangentEquiv Y : Matrix27) -
        (compactTangentEquiv Y : Matrix27) * (compactTangentEquiv X : Matrix27) := by
  rw [← GroupLieAlgebra.bracket_def X Y]
  have h := compactTangentMatrixLieHom.map_lie X Y
  simpa only [compactTangentMatrixLieHom_apply, LieRing.of_associative_ring_bracket] using h

def compactTangentRealFormLieEquiv :
    GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent ≃ₗ⁅ℝ⁆ compactRealForm :=
  compactTangentLieEquiv.trans compactMatrixEquiv.symm

end

end Math.E6.Minuscule
