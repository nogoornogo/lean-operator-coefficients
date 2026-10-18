import GUT.SU6.Embeddings.WeakDoubletEmbeddingClassification

open Math

/-!
# Matrix-level differential bridge for semisimple embedding classification

This file packages the precise differential data needed to pass from an
actual `SU(3) x SU(2) -> SU(6)` matrix embedding to the representation-level
compact-real differentials used by the checked semisimple embedding classification decomposition theorem.

The certificate is deliberately chart-free: it records the derivative at zero
of the embedding on every compact one-parameter subgroup.  It does not assert
that a merely continuous homomorphism is differentiable.  A smooth or
algebraic source category can close that remaining source step by constructing
`OneParameterDifferentiableEmbedding` for its underlying matrix embedding.
-/

namespace GUT
namespace EmbeddingDifferentialBridge

noncomputable section

open CompactEmbeddingClassification CompactProductFactorization
  DifferentiatedRepresentationBridge ProductFactorization
open SpecialUnitaryLieAlgebra
open OneParameterSubgroup
open NormedSpace
open scoped Matrix.Norms.L2Operator

abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ
abbrev E6 := EuclideanRepSpace
abbrev CoordinateEnd6 :=
  CoordinateSpace (V := E6) →L[ℂ] CoordinateSpace (V := E6)

/-- The concrete matrix action, transported to the canonical coordinates used
by the abstract differentiation bridge. -/
def matrixToCoordinateEnd : Matrix6 →ₗ[ℂ] CoordinateEnd6 :=
  DifferentiatedRepresentationBridge.coordinateEndomorphismEquiv.toLinearMap.comp
    Matrix.toEuclideanLin.toLinearMap

def matrixToCoordinateEndReal : Matrix6 →ₗ[ℝ] CoordinateEnd6 :=
  matrixToCoordinateEnd.restrictScalars ℝ

set_option linter.style.haveILetI false in
/-- A derivative identity for a matrix curve remains valid after transport to
the canonical coordinate endomorphism used by the representation bridge. -/
theorem matrixToCoordinateEnd_hasRealDerivAt
    {f : ℝ → Matrix6} {M : Matrix6} {t : ℝ}
    (h : HasRealDerivAt f M t) :
    HasRealDerivAt (fun s => matrixToCoordinateEnd (f s))
      (matrixToCoordinateEnd M) t := by
  let A := CoordinateEnd6
  letI hNormedAddM : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAddM.toAddCommGroup
  letI : NormedSpace ℝ Matrix6 := NormedAlgebra.toNormedSpace Matrix6
  letI hNormedAddA : NormedAddCommGroup A :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup A := hNormedAddA.toAddCommGroup
  letI : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A
  change HasDerivAt f M t at h
  change HasDerivAt (fun s => matrixToCoordinateEnd (f s))
    (matrixToCoordinateEnd M) t
  let T : Matrix6 →L[ℝ] A :=
    { toFun := matrixToCoordinateEnd
      map_add' := by
        intro X Y
        exact map_add matrixToCoordinateEnd X Y
      map_smul' := by
        intro r X
        change matrixToCoordinateEnd ((r : ℂ) • X) =
          (r : ℂ) • matrixToCoordinateEnd X
        exact map_smul matrixToCoordinateEnd (r : ℂ) X
      cont := by
        exact LinearMap.continuous_of_finiteDimensional _ }
  exact T.hasFDerivAt.comp_hasDerivAt t h

/-- One real-linear differential for an actual matrix embedding, verified on
all product one-parameter subgroups.  This is the exact smoothness datum semisimple embedding classification
uses; bracket preservation is derived later from the homomorphism law. -/
structure OneParameterDifferentiableEmbedding
    (iota : ProductGroup →* SU6) where
  differential :
    (CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) →ₗ[ℝ]
      CompactRealForm (Fin 6)
  derivative_at_zero : ∀ X Y,
    HasRealDerivAt
      (fun t : ℝ =>
        ((iota
          (CompactRealForm.expSpecialUnitary (t • X),
            CompactRealForm.expSpecialUnitary (t • Y)) : SU6) : Matrix6))
      (differential (X, Y) : Matrix6) 0

namespace OneParameterDifferentiableEmbedding

variable {iota : ProductGroup →* SU6}

/-- The defining `SU(6)` Lie-algebra matrix acting on Euclidean coordinates. -/
def compactToEuclideanEnd :
    CompactRealForm (Fin 6) →ₗ[ℝ]
      RestrictScalars ℝ ℂ (Module.End ℂ E6) :=
  (Matrix.toEuclideanLin.toLinearMap.restrictScalars ℝ).comp
    CompactRealForm.toMatrixRealLinear

def colorDifferential (D : OneParameterDifferentiableEmbedding iota) :
    CompactRealForm (Fin 3) →ₗ[ℝ]
      RestrictScalars ℝ ℂ (Module.End ℂ E6) :=
  compactToEuclideanEnd.comp
    (D.differential.comp
      (LinearMap.inl ℝ (CompactRealForm (Fin 3))
        (CompactRealForm (Fin 2))))

def weakDifferential (D : OneParameterDifferentiableEmbedding iota) :
    CompactRealForm (Fin 2) →ₗ[ℝ]
      RestrictScalars ℝ ℂ (Module.End ℂ E6) :=
  compactToEuclideanEnd.comp
    (D.differential.comp
      (LinearMap.inr ℝ (CompactRealForm (Fin 3))
        (CompactRealForm (Fin 2))))

theorem color_derivative_at_zero
    (D : OneParameterDifferentiableEmbedding iota)
    (X : CompactRealForm (Fin 3)) :
    HasRealDerivAt
      (coordinateActionCurve
        (firstRestriction (euclideanDefiningRestriction iota)) X)
      (coordinateEndomorphismEquiv (D.colorDifferential X)) 0 := by
  have hMatrix := D.derivative_at_zero X 0
  have hTransport := matrixToCoordinateEnd_hasRealDerivAt hMatrix
  change HasRealDerivAt
    (fun s : ℝ => coordinateEndomorphismEquiv
      (Matrix.toEuclideanLin
        (((iota
          (CompactRealForm.expSpecialUnitary (s • X), 1) : SU6) : Matrix6))))
    (coordinateEndomorphismEquiv
      (Matrix.toEuclideanLin (D.differential (X, 0) : Matrix6))) 0
  simpa [matrixToCoordinateEnd] using hTransport

theorem weak_derivative_at_zero
    (D : OneParameterDifferentiableEmbedding iota)
    (Y : CompactRealForm (Fin 2)) :
    HasRealDerivAt
      (coordinateActionCurve
        (secondRestriction (euclideanDefiningRestriction iota)) Y)
      (coordinateEndomorphismEquiv (D.weakDifferential Y)) 0 := by
  have hMatrix := D.derivative_at_zero 0 Y
  have hTransport := matrixToCoordinateEnd_hasRealDerivAt hMatrix
  change HasRealDerivAt
    (fun s : ℝ => coordinateEndomorphismEquiv
      (Matrix.toEuclideanLin
        (((iota
          (1, CompactRealForm.expSpecialUnitary (s • Y)) : SU6) : Matrix6))))
    (coordinateEndomorphismEquiv
      (Matrix.toEuclideanLin (D.differential (0, Y) : Matrix6))) 0
  simpa [matrixToCoordinateEnd] using hTransport

/-- A single matrix-level differential of the embedding supplies the two
ambient representation certificates consumed by semisimple embedding classification. -/
def toRealLinearlyDifferentiableProductAction
    (D : OneParameterDifferentiableEmbedding iota) :
    RealLinearlyDifferentiableProductAction
      (euclideanDefiningRestriction iota) where
  colorDifferential :=
    { finiteDimensional := inferInstance
      differential := D.colorDifferential
      derivative_at_zero := D.color_derivative_at_zero }
  weakDifferential :=
    { finiteDimensional := inferInstance
      differential := D.weakDifferential
      derivative_at_zero := D.weak_derivative_at_zero }

end OneParameterDifferentiableEmbedding

/-- Conjugate an embedding by an ambient special-unitary element. -/
def conjugateEmbedding (U : SU6) (iota : ProductGroup →* SU6) :
    ProductGroup →* SU6 :=
  (MulAut.conj U).toMonoidHom.comp iota

@[simp]
theorem conjugateEmbedding_apply (U : SU6)
    (iota : ProductGroup →* SU6) (g : ProductGroup) :
    conjugateEmbedding U iota g = U * iota g * U⁻¹ :=
  rfl

/-- Ambient conjugation as a real-linear map of compact real forms. -/
def conjugateDifferential (U : SU6) :
    CompactRealForm (Fin 6) →ₗ[ℝ] CompactRealForm (Fin 6) where
  toFun := CompactRealForm.conjugate U
  map_add' := by
    intro X Y
    apply CompactRealForm.ext
    apply Subtype.ext
    change
      (U : Matrix6) * ((X : Matrix6) + (Y : Matrix6)) *
          ((U⁻¹ : SU6) : Matrix6) =
        (U : Matrix6) * (X : Matrix6) * ((U⁻¹ : SU6) : Matrix6) +
          (U : Matrix6) * (Y : Matrix6) * ((U⁻¹ : SU6) : Matrix6)
    noncomm_ring
  map_smul' := by
    intro t X
    apply CompactRealForm.ext
    apply Subtype.ext
    change
      (U : Matrix6) * ((t : ℂ) • (X : Matrix6)) *
          ((U⁻¹ : SU6) : Matrix6) =
        (t : ℂ) •
          ((U : Matrix6) * (X : Matrix6) * ((U⁻¹ : SU6) : Matrix6))
    simp only [smul_mul_assoc, mul_smul_comm]

set_option linter.style.haveILetI false in
/-- Conjugating the target preserves the matrix one-parameter differential
certificate. -/
def OneParameterDifferentiableEmbedding.targetConjugate
    {iota : ProductGroup →* SU6}
    (D : OneParameterDifferentiableEmbedding iota) (U : SU6) :
    OneParameterDifferentiableEmbedding (conjugateEmbedding U iota) where
  differential := (conjugateDifferential U).comp D.differential
  derivative_at_zero := by
    intro X Y
    have h := D.derivative_at_zero X Y
    letI hNormedAdd : NormedAddCommGroup Matrix6 :=
      NonUnitalNormedRing.toNormedAddCommGroup
    letI : AddCommGroup Matrix6 := hNormedAdd.toAddCommGroup
    change HasDerivAt
      (fun t : ℝ =>
        (U : Matrix6) *
          ((iota
            (CompactRealForm.expSpecialUnitary (t • X),
              CompactRealForm.expSpecialUnitary (t • Y)) : SU6) : Matrix6) *
          ((U⁻¹ : SU6) : Matrix6))
      ((U : Matrix6) * (D.differential (X, Y) : Matrix6) *
        ((U⁻¹ : SU6) : Matrix6)) 0
    change HasDerivAt
      (fun t : ℝ =>
        ((iota
          (CompactRealForm.expSpecialUnitary (t • X),
            CompactRealForm.expSpecialUnitary (t • Y)) : SU6) : Matrix6))
      (D.differential (X, Y) : Matrix6) 0 at h
    exact (h.const_mul (U : Matrix6)).mul_const ((U⁻¹ : SU6) : Matrix6)

/-- Ambient conjugation preserves continuity of the embedding. -/
def conjugateContinuousEmbedding (U : SU6)
    (iota : ProductGroup →ₜ* SU6) : ProductGroup →ₜ* SU6 where
  toMonoidHom := conjugateEmbedding U iota
  continuous_toFun := by
    exact (continuous_const.mul iota.continuous).mul continuous_const

/-- The classified semisimple embedding classification decomposition from a concrete one-parameter differential
of the actual matrix embedding. -/
theorem injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_oneParameterDifferentiableEmbedding
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (D : OneParameterDifferentiableEmbedding
      (iota : ProductGroup →* SU6)) :
    Nonempty (WeakDoubletEmbeddingClassification.ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :=
  WeakDoubletEmbeddingClassification.injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_realLinearlyDifferentiableProductAction
    iota hInjective Y hCommute hNontrivial
      D.toRealLinearlyDifferentiableProductAction

/-- The numerical semisimple embedding classification classification from the same concrete matrix-level
differential certificate. -/
theorem injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_oneParameterDifferentiableEmbedding
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1)
    (D : OneParameterDifferentiableEmbedding
      (iota : ProductGroup →* SU6)) :
    ∃ B : LowDimensionalIrreps.SixDimensionalBlockDecomposition,
      B.toBranchCounts.IsWeakDoubletBlock :=
  WeakDoubletEmbeddingClassification.injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_realLinearlyDifferentiableProductAction
    iota hInjective Y hCommute hNontrivial
      D.toRealLinearlyDifferentiableProductAction

end
end EmbeddingDifferentialBridge
end GUT
