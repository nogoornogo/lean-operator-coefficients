import GUT.SU6.Embeddings.EmbeddingDifferentialBridge
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open Math

/-!
# Smooth matrix-embedding bridge for semisimple embedding classification

This file turns ordinary first-order differentiability in exponential
coordinates into the matrix one-parameter certificate consumed by the semisimple embedding classification
classification.  The derivative is initially matrix-valued.  Because the
curve itself lies in `SU(6)`, differentiating unitarity and determinant one
shows that its derivative automatically lies in the compact real form
`su(6)`.
-/

namespace GUT
namespace SmoothEmbeddingBridge

noncomputable section

open CompactEmbeddingClassification EmbeddingDifferentialBridge
open SpecialUnitaryLieAlgebra OneParameterSubgroup
open NormedSpace
open scoped Matrix.Norms.L2Operator

abbrev SourceLie :=
  CompactRealForm (Fin 3) × CompactRealForm (Fin 2)

local instance sourceLieAddCommGroup : AddCommGroup SourceLie :=
  (inferInstance : NormedAddCommGroup SourceLie).toAddCommGroup
local instance sourceLieModuleReal : Module ℝ SourceLie :=
  (inferInstance : NormedSpace ℝ SourceLie).toModule

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℂ

local instance matrix3NormedAddCommGroup : NormedAddCommGroup Matrix3 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance matrix3AddCommGroup : AddCommGroup Matrix3 :=
  matrix3NormedAddCommGroup.toAddCommGroup
local instance matrix3NormedSpaceReal : NormedSpace ℝ Matrix3 :=
  NormedAlgebra.toNormedSpace Matrix3
local instance matrix3ModuleReal : Module ℝ Matrix3 :=
  matrix3NormedSpaceReal.toModule
local instance matrix2NormedAddCommGroup : NormedAddCommGroup Matrix2 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance matrix2AddCommGroup : AddCommGroup Matrix2 :=
  matrix2NormedAddCommGroup.toAddCommGroup
local instance matrix2NormedSpaceReal : NormedSpace ℝ Matrix2 :=
  NormedAlgebra.toNormedSpace Matrix2
local instance matrix2ModuleReal : Module ℝ Matrix2 :=
  matrix2NormedSpaceReal.toModule
local instance matrix6NormedAddCommGroup : NormedAddCommGroup Matrix6 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance matrix6AddCommGroup : AddCommGroup Matrix6 :=
  matrix6NormedAddCommGroup.toAddCommGroup
local instance matrix6NormedSpaceReal : NormedSpace ℝ Matrix6 :=
  NormedAlgebra.toNormedSpace Matrix6
local instance matrix6ModuleReal : Module ℝ Matrix6 :=
  matrix6NormedSpaceReal.toModule

abbrev SourceMatrix := Matrix3 × Matrix2

/-- Inclusion of the compact source Lie algebra into the two ambient complex
matrix spaces. -/
def sourceTangentLinear : SourceLie →ₗ[ℝ] SourceMatrix :=
  { toFun := fun Z => ((Z.1 : Matrix3), (Z.2 : Matrix2))
    map_add' := by
      intro X Y
      rfl
    map_smul' := by
      intro t X
      rfl }

def sourceTangentInclusion : SourceLie →L[ℝ] SourceMatrix :=
  { sourceTangentLinear with
    cont := LinearMap.continuous_of_finiteDimensional sourceTangentLinear }

/-- The pair of ordinary matrix exponentials on the source compact real
form. -/
def sourceExponentialMatrix (Z : SourceLie) : SourceMatrix :=
  (NormedSpace.exp (Z.1 : Matrix3), NormedSpace.exp (Z.2 : Matrix2))

@[simp]
theorem sourceExponentialMatrix_zero :
    sourceExponentialMatrix 0 = (1 : SourceMatrix) := by
  simp [sourceExponentialMatrix]

set_option backward.isDefEq.respectTransparency false in
/-- The source matrix exponential has derivative equal to the tangent-space
inclusion at zero. -/
theorem sourceExponentialMatrix_hasFDerivAt_zero :
    HasFDerivAt sourceExponentialMatrix sourceTangentInclusion 0 := by
  let colorLinear : SourceLie →ₗ[ℝ] Matrix3 :=
    { toFun := fun Z => (Z.1 : Matrix3)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let colorInclusion : SourceLie →L[ℝ] Matrix3 :=
    { colorLinear with
      cont := LinearMap.continuous_of_finiteDimensional colorLinear }
  let weakLinear : SourceLie →ₗ[ℝ] Matrix2 :=
    { toFun := fun Z => (Z.2 : Matrix2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let weakInclusion : SourceLie →L[ℝ] Matrix2 :=
    { weakLinear with
      cont := LinearMap.continuous_of_finiteDimensional weakLinear }
  have hColorExp :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix3)).comp
      0 colorInclusion.hasFDerivAt
  have hWeakExp :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix2)).comp
      0 weakInclusion.hasFDerivAt
  have hPair := hColorExp.prodMk hWeakExp
  convert hPair using 1 <;> try rfl

/-- The matrix-valued expression of an embedding in exponential coordinates
around the identity of `SU(3) x SU(2)`. -/
def exponentialChartMap (iota : ProductGroup →* SU6) (Z : SourceLie) :
    Matrix6 :=
  ((iota
    (CompactRealForm.expSpecialUnitary Z.1,
      CompactRealForm.expSpecialUnitary Z.2) : SU6) : Matrix6)

@[simp]
theorem exponentialChartMap_zero (iota : ProductGroup →* SU6) :
    exponentialChartMap iota 0 = 1 := by
  unfold exponentialChartMap
  have hSource :
      (CompactRealForm.expSpecialUnitary (0 : SourceLie).1,
        CompactRealForm.expSpecialUnitary (0 : SourceLie).2) =
        (1 : ProductGroup) := by
    apply Prod.ext <;> simp
  rw [hSource, iota.map_one]
  rfl

/-- First-order smoothness of a matrix embedding at the identity, expressed
in the canonical exponential coordinates on the source. -/
structure ExponentialChartDifferentiableEmbedding
    (iota : ProductGroup →* SU6) where
  derivative : SourceLie →L[ℝ] Matrix6
  hasFDerivAt_zero : HasFDerivAt (exponentialChartMap iota) derivative 0

/-- A source condition convenient for matrix-algebraic and ordinary smooth
models: the group homomorphism is the restriction of a real-differentiable
ambient matrix map near the identity. -/
structure AmbientlyDifferentiableEmbedding
    (iota : ProductGroup →* SU6) where
  extension : SourceMatrix → Matrix6
  agrees_on_group : ∀ g : ProductGroup,
    extension ((g.1 : Matrix3), (g.2 : Matrix2)) = (iota g : Matrix6)
  differentiableAt_identity :
    DifferentiableAt ℝ extension (1 : SourceMatrix)

namespace AmbientlyDifferentiableEmbedding

variable {iota : ProductGroup →* SU6}

/-- An ambiently differentiable matrix embedding is differentiable in source
exponential coordinates. -/
def toExponentialChartDifferentiableEmbedding
    (D : AmbientlyDifferentiableEmbedding iota) :
    ExponentialChartDifferentiableEmbedding iota where
  derivative :=
    (fderiv ℝ D.extension (1 : SourceMatrix)).comp sourceTangentInclusion
  hasFDerivAt_zero := by
    have hExtension := D.differentiableAt_identity.hasFDerivAt
    have hExtensionAt : HasFDerivAt D.extension
        (fderiv ℝ D.extension (1 : SourceMatrix))
        (sourceExponentialMatrix 0) := by
      rw [sourceExponentialMatrix_zero]
      exact hExtension
    have hComp := hExtensionAt.comp 0 sourceExponentialMatrix_hasFDerivAt_zero
    apply hComp.congr_of_eventuallyEq
    filter_upwards [] with Z
    symm
    simpa [Function.comp_def, sourceExponentialMatrix, exponentialChartMap] using
      D.agrees_on_group
        (CompactRealForm.expSpecialUnitary Z.1,
          CompactRealForm.expSpecialUnitary Z.2)

end AmbientlyDifferentiableEmbedding

namespace ExponentialChartDifferentiableEmbedding

variable {iota : ProductGroup →* SU6}

/-- The certificate extracted from mathlib's ordinary Frechet
differentiability predicate. -/
def ofDifferentiableAt
    (h : DifferentiableAt ℝ (exponentialChartMap iota) 0) :
    ExponentialChartDifferentiableEmbedding iota where
  derivative := fderiv ℝ (exponentialChartMap iota) 0
  hasFDerivAt_zero := h.hasFDerivAt

set_option linter.style.haveILetI false in
/-- Frechet differentiability in exponential coordinates supplies every
one-parameter directional derivative. -/
theorem line_hasRealDerivAt
    (D : ExponentialChartDifferentiableEmbedding iota) (Z : SourceLie) :
    HasRealDerivAt
      (fun t : ℝ => exponentialChartMap iota (t • Z))
      (D.derivative Z) 0 := by
  letI hNormedAdd : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAdd.toAddCommGroup
  change HasDerivAt
    (fun t : ℝ => exponentialChartMap iota (t • Z))
    (D.derivative Z) 0
  have hLine : HasDerivAt (fun t : ℝ => t • Z) Z 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).smul_const Z
  exact D.hasFDerivAt_zero.comp_hasDerivAt_of_eq 0 hLine (by simp)

set_option linter.style.haveILetI false in
/-- The derivative of an `SU(6)`-valued differentiable curve at the identity
is skew-adjoint. -/
theorem derivative_mem_skewAdjoint
    (D : ExponentialChartDifferentiableEmbedding iota) (Z : SourceLie) :
    D.derivative Z ∈ skewAdjoint Matrix6 := by
  letI hNormedAdd : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAdd.toAddCommGroup
  let f : ℝ → Matrix6 := fun t => exponentialChartMap iota (t • Z)
  have hCurve : HasDerivAt f (D.derivative Z) 0 := by
    exact D.line_hasRealDerivAt Z
  have hf0 : f 0 = 1 := by
    simp [f]
  have hProduct := hCurve.star.mul hCurve
  have hConstant : HasDerivAt (fun t : ℝ => star (f t) * f t) 0 0 := by
    apply (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : Matrix6))).congr_of_eventuallyEq
    filter_upwards [] with t
    exact Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup
        ((iota
          (CompactRealForm.expSpecialUnitary (t • Z).1,
            CompactRealForm.expSpecialUnitary (t • Z).2)).property))
  have hZero := hProduct.unique hConstant
  simp only [hf0, star_one, mul_one, one_mul] at hZero
  rw [skewAdjoint.mem_iff]
  apply eq_neg_of_add_eq_zero_left
  exact hZero

set_option linter.style.haveILetI false in
/-- The derivative of an `SU(6)`-valued differentiable curve at the identity
is traceless. -/
theorem derivative_trace_eq_zero
    (D : ExponentialChartDifferentiableEmbedding iota) (Z : SourceLie) :
    Matrix.trace (D.derivative Z) = 0 := by
  letI hNormedAdd : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAdd.toAddCommGroup
  let f : ℝ → Matrix6 := fun t => exponentialChartMap iota (t • Z)
  have hCurve : HasDerivAt f (D.derivative Z) 0 := by
    exact D.line_hasRealDerivAt Z
  have hDetReal :=
    (MatrixDeterminantExponential.hasFDerivAt_det_one
      (n := Fin 6)).restrictScalars ℝ
  have hDetCurve := hDetReal.comp_hasDerivAt_of_eq 0 hCurve (by
    simp [f])
  have hConstant : HasDerivAt (fun t : ℝ => Matrix.det (f t)) 0 0 := by
    apply (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℂ))).congr_of_eventuallyEq
    filter_upwards [] with t
    change Matrix.det
      (((iota
        (CompactRealForm.expSpecialUnitary (t • Z).1,
          CompactRealForm.expSpecialUnitary (t • Z).2) : SU6) : Matrix6)) = 1
    exact
      (iota
        (CompactRealForm.expSpecialUnitary (t • Z).1,
          CompactRealForm.expSpecialUnitary (t • Z).2)).property.2
  simpa using hDetCurve.unique hConstant

/-- The ambient derivative, now certified as a point of the compact target
Lie algebra. -/
def tangentValue
    (D : ExponentialChartDifferentiableEmbedding iota) (Z : SourceLie) :
    CompactRealForm (Fin 6) where
  toSpecialLinear := ⟨D.derivative Z, D.derivative_trace_eq_zero Z⟩
  skewAdjoint := D.derivative_mem_skewAdjoint Z

@[simp]
theorem coe_tangentValue
    (D : ExponentialChartDifferentiableEmbedding iota) (Z : SourceLie) :
    (D.tangentValue Z : Matrix6) = D.derivative Z :=
  rfl

/-- The matrix derivative corestricts to a real-linear map into `su(6)`. -/
def tangentDifferential
    (D : ExponentialChartDifferentiableEmbedding iota) :
    SourceLie →ₗ[ℝ] CompactRealForm (Fin 6) where
  toFun := D.tangentValue
  map_add' := by
    intro X Y
    apply CompactRealForm.ext
    apply Subtype.ext
    exact D.derivative.map_add X Y
  map_smul' := by
    intro t X
    apply CompactRealForm.ext
    apply Subtype.ext
    exact D.derivative.map_smul t X

/-- Exponential-chart differentiability is sufficient for the exact
one-parameter differential certificate used by semisimple embedding classification. -/
def toOneParameterDifferentiableEmbedding
    (D : ExponentialChartDifferentiableEmbedding iota) :
    OneParameterDifferentiableEmbedding iota where
  differential := D.tangentDifferential
  derivative_at_zero := by
    intro X Y
    change HasRealDerivAt
      (fun t : ℝ =>
        ((iota
          (CompactRealForm.expSpecialUnitary (t • X),
            CompactRealForm.expSpecialUnitary (t • Y)) : SU6) : Matrix6))
      (D.derivative (X, Y)) 0
    simpa [exponentialChartMap] using D.line_hasRealDerivAt (X, Y)

end ExponentialChartDifferentiableEmbedding

namespace AmbientlyDifferentiableEmbedding

variable {iota : ProductGroup →* SU6}

/-- The complete existing semisimple embedding classification differential certificate obtained from an
ambient first-order smoothness witness. -/
def toOneParameterDifferentiableEmbedding
    (D : AmbientlyDifferentiableEmbedding iota) :
    OneParameterDifferentiableEmbedding iota :=
  D.toExponentialChartDifferentiableEmbedding.toOneParameterDifferentiableEmbedding

end AmbientlyDifferentiableEmbedding

/-- The classified semisimple embedding classification decomposition for an ambiently differentiable compact
matrix embedding with a nontrivial commuting hypercharge circle. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_ambientlyDifferentiable
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (D : AmbientlyDifferentiableEmbedding
      (iota : ProductGroup →* SU6)) :
    Nonempty (WeakDoubletEmbeddingClassification.ClassifiedWeakDoubletDecomposition
      (CompactEmbeddingClassification.euclideanDefiningRestriction
        (iota : ProductGroup →* SU6))) :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_oneParameterDifferentiableEmbedding
    iota hInjective Y hCommute hNontrivial
      D.toOneParameterDifferentiableEmbedding

/-- The numerical semisimple embedding classification branch classification under the same ordinary smooth
matrix-embedding source condition. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_ambientlyDifferentiable
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (D : AmbientlyDifferentiableEmbedding
      (iota : ProductGroup →* SU6)) :
    ∃ B : LowDimensionalIrreps.SixDimensionalBlockDecomposition,
      B.toBranchCounts.IsWeakDoubletBlock :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_oneParameterDifferentiableEmbedding
    iota hInjective Y hCommute hNontrivial
      D.toOneParameterDifferentiableEmbedding

/-- The classified semisimple embedding classification decomposition stated directly with mathlib's ordinary
first-order differentiability predicate in source exponential coordinates. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_exponentialChartDifferentiableAt
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (hDifferentiable : DifferentiableAt ℝ
      (exponentialChartMap (iota : ProductGroup →* SU6)) 0) :
    Nonempty (WeakDoubletEmbeddingClassification.ClassifiedWeakDoubletDecomposition
      (CompactEmbeddingClassification.euclideanDefiningRestriction
        (iota : ProductGroup →* SU6))) :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_oneParameterDifferentiableEmbedding
    iota hInjective Y hCommute hNontrivial
      (ExponentialChartDifferentiableEmbedding.ofDifferentiableAt
        hDifferentiable).toOneParameterDifferentiableEmbedding

/-- The numerical semisimple embedding classification branch classification under the same explicit
first-order smoothness condition. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_exponentialChartDifferentiableAt
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (hDifferentiable : DifferentiableAt ℝ
      (exponentialChartMap (iota : ProductGroup →* SU6)) 0) :
    ∃ B : LowDimensionalIrreps.SixDimensionalBlockDecomposition,
      B.toBranchCounts.IsWeakDoubletBlock :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_oneParameterDifferentiableEmbedding
    iota hInjective Y hCommute hNontrivial
      (ExponentialChartDifferentiableEmbedding.ofDifferentiableAt
        hDifferentiable).toOneParameterDifferentiableEmbedding

end
end SmoothEmbeddingBridge
end GUT
