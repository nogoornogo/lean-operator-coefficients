import GUT.SU6.SelectionRules.FlippedBranch.ColorNeutralSMGroup
import GUT.SU6.Embeddings.EmbeddingDifferentialBridge
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The differentiable standard semisimple embedding

This file constructs the concrete block embedding

`SU(3) x SU(2) -> SU(6),  (A, B) |-> diag(A, B, 1)`

as an injective continuous homomorphism.  Its compact-real differential is the
block map `(X, Y) |-> diag(X, Y, 0)`.  The matrix exponential derivative proves
that this map supplies the `OneParameterDifferentiableEmbedding` certificate
used by the semisimple embedding classification classification bridge.  Thus the differential interface is
inhabited by the intended standard block model, independently of the still
open theorem upgrading every admissible embedding to such a certificate.
-/

namespace GUT
namespace StandardSemisimpleEmbedding

noncomputable section

open CompactEmbeddingClassification
open SpecialUnitaryLieAlgebra
open EmbeddingDifferentialBridge
open scoped Matrix.Norms.L2Operator

def weakToUnitary : SU2 →* ColorNeutralSMGroup.U2 where
  toFun h := ⟨h, Matrix.specialUnitaryGroup_le_unitaryGroup h.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def toColorNeutral : ProductGroup →* ColorNeutralSMGroup.Group where
  toFun g := (g.1, weakToUnitary g.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def embedding : ProductGroup →* SU6 :=
  ColorNeutralSMGroup.embedding.comp toColorNeutral

theorem embedding_injective : Function.Injective embedding := by
  intro g h heq
  have hpair : toColorNeutral g = toColorNeutral h :=
    ColorNeutralSMGroup.embedding_injective heq
  have hfst : g.1 = h.1 :=
    congrArg (fun p : ColorNeutralSMGroup.Group => p.1) hpair
  have hsnd : weakToUnitary g.2 = weakToUnitary h.2 :=
    congrArg (fun p : ColorNeutralSMGroup.Group => p.2) hpair
  apply Prod.ext hfst
  apply Subtype.ext
  exact congrArg
    (fun u : ColorNeutralSMGroup.U2 =>
      (u : Matrix (Fin 2) (Fin 2) ℂ)) hsnd

theorem continuous_embedding : Continuous embedding := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : ProductGroup =>
    Matrix.reindex ColorNeutralSMGroup.blockIndexEquiv
      ColorNeutralSMGroup.blockIndexEquiv
      (ColorNeutralSMGroup.rawEmbeddingMatrix (toColorNeutral g)))
  unfold ColorNeutralSMGroup.rawEmbeddingMatrix
    ColorNeutralSMGroup.singletBlock toColorNeutral weakToUnitary
  fun_prop

def continuousEmbedding : ProductGroup →ₜ* SU6 where
  toMonoidHom := embedding
  continuous_toFun := continuous_embedding

abbrev BlockIndex := ColorNeutralSMGroup.BlockIndex
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ

def rawBlockMatrix (AB : Matrix3 × Matrix2) :
    Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks AB.1 0 0
    (Matrix.fromBlocks AB.2 0 0 (0 : Matrix (Fin 1) (Fin 1) ℂ))

def blockMatrix (AB : Matrix3 × Matrix2) : Matrix6 :=
  Matrix.reindex ColorNeutralSMGroup.blockIndexEquiv
    ColorNeutralSMGroup.blockIndexEquiv (rawBlockMatrix AB)

def rawSingletMatrix : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks (0 : Matrix3) 0 0
    (Matrix.fromBlocks (0 : Matrix2) 0 0
      (1 : Matrix (Fin 1) (Fin 1) ℂ))

def singletMatrix : Matrix6 :=
  Matrix.reindex ColorNeutralSMGroup.blockIndexEquiv
    ColorNeutralSMGroup.blockIndexEquiv rawSingletMatrix

theorem rawBlockMatrix_add (A B : Matrix3 × Matrix2) :
    rawBlockMatrix (A + B) = rawBlockMatrix A + rawBlockMatrix B := by
  change
    Matrix.fromBlocks (A.1 + B.1) 0 0
        (Matrix.fromBlocks (A.2 + B.2) 0 0 0) =
      rawBlockMatrix A + rawBlockMatrix B
  have hInner :
      Matrix.fromBlocks (A.2 + B.2) 0 0
          (0 : Matrix (Fin 1) (Fin 1) ℂ) =
        Matrix.fromBlocks A.2 0 0 0 + Matrix.fromBlocks B.2 0 0 0 := by
    simpa only [zero_add] using
      (Matrix.fromBlocks_add A.2 0 0
        (0 : Matrix (Fin 1) (Fin 1) ℂ) B.2 0 0 0).symm
  rw [hInner]
  simpa only [rawBlockMatrix, zero_add] using
    (Matrix.fromBlocks_add A.1 0 0
      (Matrix.fromBlocks A.2 0 0 0) B.1 0 0
      (Matrix.fromBlocks B.2 0 0 0)).symm

theorem rawBlockMatrix_smul (t : ℝ) (A : Matrix3 × Matrix2) :
    rawBlockMatrix (t • A) = t • rawBlockMatrix A := by
  change
    Matrix.fromBlocks (t • A.1) 0 0
        (Matrix.fromBlocks (t • A.2) 0 0 0) =
      t • Matrix.fromBlocks A.1 0 0 (Matrix.fromBlocks A.2 0 0 0)
  rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul]
  simp

def blockMatrixLinear : (Matrix3 × Matrix2) →ₗ[ℝ] Matrix6 where
  toFun := blockMatrix
  map_add' := by
    intro A B
    change
      (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv) (rawBlockMatrix (A + B)) =
      (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv) (rawBlockMatrix A) +
      (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv) (rawBlockMatrix B)
    rw [rawBlockMatrix_add, map_add]
  map_smul' := by
    intro t A
    change
      (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv) (rawBlockMatrix (t • A)) =
      t •
        (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
          ColorNeutralSMGroup.blockIndexEquiv) (rawBlockMatrix A)
    rw [rawBlockMatrix_smul, map_smul]

def blockMatrixContinuousLinear : (Matrix3 × Matrix2) →L[ℝ] Matrix6 :=
  { toLinearMap := blockMatrixLinear
    cont := LinearMap.continuous_of_finiteDimensional _ }

theorem real_smul_matrix_eq_complex_smul
    {n : Type*} (t : ℝ) (A : Matrix n n ℂ) :
    t • A = (t : ℂ) • A := by
  ext i j
  simp [Complex.real_smul]

theorem singletBlock_weakToUnitary_eq_one (h : SU2) :
    ColorNeutralSMGroup.singletBlock (weakToUnitary h) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  have hdet : Matrix.det (h : Matrix2) = 1 := h.prop.2
  change star (Matrix.det (h : Matrix2)) = 1
  rw [hdet]
  simp

theorem embedding_coe (g : ProductGroup) :
    ((embedding g : SU6) : Matrix6) =
      blockMatrix ((g.1 : Matrix3), (g.2 : Matrix2)) + singletMatrix := by
  change
    (Matrix.reindexLinearEquiv ℂ ℂ ColorNeutralSMGroup.blockIndexEquiv
      ColorNeutralSMGroup.blockIndexEquiv)
        (ColorNeutralSMGroup.rawEmbeddingMatrix (toColorNeutral g)) =
      (Matrix.reindexLinearEquiv ℂ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv)
          (rawBlockMatrix ((g.1 : Matrix3), (g.2 : Matrix2))) +
      (Matrix.reindexLinearEquiv ℂ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv) rawSingletMatrix
  rw [← map_add]
  congr 1
  change
    Matrix.fromBlocks (g.1 : Matrix3) 0 0
        (Matrix.fromBlocks (g.2 : Matrix2) 0 0
          (ColorNeutralSMGroup.singletBlock (weakToUnitary g.2))) =
      rawBlockMatrix ((g.1 : Matrix3), (g.2 : Matrix2)) + rawSingletMatrix
  rw [singletBlock_weakToUnitary_eq_one]
  rw [rawBlockMatrix, rawSingletMatrix, Matrix.fromBlocks_add,
    Matrix.fromBlocks_add]
  simp

def rawDifferentialMatrix
    (XY : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    Matrix BlockIndex BlockIndex ℂ :=
  rawBlockMatrix ((XY.1 : Matrix3), (XY.2 : Matrix2))

def differentialMatrix
    (XY : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  blockMatrix ((XY.1 : Matrix3), (XY.2 : Matrix2))

theorem trace_reindex_self
    {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  rw [Matrix.trace, Matrix.trace]
  exact (Fintype.sum_equiv e
    (fun i => A i i)
    (fun j => Matrix.reindex e e A j j)
    (fun i => by simp [Matrix.reindex_apply])).symm

theorem trace_fromBlocks_zero
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 D) =
      Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem differentialMatrix_trace
    (XY : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    Matrix.trace (differentialMatrix XY) = 0 := by
  have hColor : Matrix.trace (XY.1 : Matrix (Fin 3) (Fin 3) ℂ) = 0 :=
    XY.1.toSpecialLinear.2
  have hWeak : Matrix.trace (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) = 0 :=
    XY.2.toSpecialLinear.2
  rw [differentialMatrix, blockMatrix, trace_reindex_self,
    rawBlockMatrix, trace_fromBlocks_zero,
    trace_fromBlocks_zero, Matrix.trace_zero, add_zero,
    hColor, hWeak, zero_add]

theorem differentialMatrix_skewAdjoint
    (XY : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    differentialMatrix XY ∈ skewAdjoint (Matrix (Fin 6) (Fin 6) ℂ) := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    differentialMatrix, blockMatrix, Matrix.conjTranspose_reindex]
  simp only [rawBlockMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero]
  rw [show Matrix.conjTranspose (XY.1 : Matrix (Fin 3) (Fin 3) ℂ) =
      -(XY.1 : Matrix (Fin 3) (Fin 3) ℂ) by
        exact skewAdjoint.mem_iff.mp XY.1.skewAdjoint,
    show Matrix.conjTranspose (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) =
      -(XY.2 : Matrix (Fin 2) (Fin 2) ℂ) by
        exact skewAdjoint.mem_iff.mp XY.2.skewAdjoint]
  have hInner :
      Matrix.fromBlocks (-(XY.2 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
          (0 : Matrix (Fin 1) (Fin 1) ℂ) =
        -Matrix.fromBlocks (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0 := by
    simpa only [neg_zero] using
      (Matrix.fromBlocks_neg (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        (0 : Matrix (Fin 1) (Fin 1) ℂ)).symm
  rw [hInner]
  have hOuter :
      Matrix.fromBlocks (-(XY.1 : Matrix (Fin 3) (Fin 3) ℂ)) 0 0
          (-Matrix.fromBlocks (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
            (0 : Matrix (Fin 1) (Fin 1) ℂ)) =
        -Matrix.fromBlocks (XY.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
          (Matrix.fromBlocks (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0) := by
    simpa only [neg_zero] using
      (Matrix.fromBlocks_neg (XY.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
        (Matrix.fromBlocks (XY.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
          (0 : Matrix (Fin 1) (Fin 1) ℂ))).symm
  rw [hOuter]
  ext i j
  rfl

def differentialValue
    (XY : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    CompactRealForm (Fin 6) where
  toSpecialLinear := ⟨differentialMatrix XY, differentialMatrix_trace XY⟩
  skewAdjoint := differentialMatrix_skewAdjoint XY

theorem differentialMatrix_add
    (A B : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    differentialMatrix (A + B) =
      differentialMatrix A + differentialMatrix B := by
  change
    (Matrix.reindexLinearEquiv ℂ ℂ ColorNeutralSMGroup.blockIndexEquiv
      ColorNeutralSMGroup.blockIndexEquiv) (rawDifferentialMatrix (A + B)) =
    (Matrix.reindexLinearEquiv ℂ ℂ ColorNeutralSMGroup.blockIndexEquiv
      ColorNeutralSMGroup.blockIndexEquiv) (rawDifferentialMatrix A) +
    (Matrix.reindexLinearEquiv ℂ ℂ ColorNeutralSMGroup.blockIndexEquiv
      ColorNeutralSMGroup.blockIndexEquiv) (rawDifferentialMatrix B)
  rw [← map_add]
  congr 1
  change
    Matrix.fromBlocks
      ((A.1 : Matrix (Fin 3) (Fin 3) ℂ) + (B.1 : Matrix (Fin 3) (Fin 3) ℂ))
      0 0
      (Matrix.fromBlocks
        ((A.2 : Matrix (Fin 2) (Fin 2) ℂ) + (B.2 : Matrix (Fin 2) (Fin 2) ℂ))
        0 0 0) =
      rawDifferentialMatrix A + rawDifferentialMatrix B
  have hInner :
      Matrix.fromBlocks
          ((A.2 : Matrix (Fin 2) (Fin 2) ℂ) +
            (B.2 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
          (0 : Matrix (Fin 1) (Fin 1) ℂ) =
        Matrix.fromBlocks (A.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0 +
          Matrix.fromBlocks (B.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0 := by
    simpa only [zero_add] using
      (Matrix.fromBlocks_add
        (A.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (B.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0).symm
  rw [hInner]
  simpa only [rawDifferentialMatrix, rawBlockMatrix, zero_add] using
    (Matrix.fromBlocks_add
      (A.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      (Matrix.fromBlocks (A.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0)
      (B.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
      (Matrix.fromBlocks (B.2 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 0)).symm

theorem differentialMatrix_smul
    (t : ℝ) (A : CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) :
    differentialMatrix (t • A) = t • differentialMatrix A := by
  change
    (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
      ColorNeutralSMGroup.blockIndexEquiv) (rawDifferentialMatrix (t • A)) =
    t •
      (Matrix.reindexLinearEquiv ℝ ℂ ColorNeutralSMGroup.blockIndexEquiv
        ColorNeutralSMGroup.blockIndexEquiv) (rawDifferentialMatrix A)
  rw [← map_smul]
  congr 1
  simp only [rawDifferentialMatrix, Prod.smul_fst, Prod.smul_snd,
    CompactRealForm.coe_real_smul]
  rw [rawBlockMatrix]
  change
    Matrix.fromBlocks ((t : ℂ) • (A.1 : Matrix3)) 0 0
        (Matrix.fromBlocks ((t : ℂ) • (A.2 : Matrix2)) 0 0 0) =
      t • Matrix.fromBlocks (A.1 : Matrix3) 0 0
        (Matrix.fromBlocks (A.2 : Matrix2) 0 0 0)
  rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul]
  simp

def differential :
    (CompactRealForm (Fin 3) × CompactRealForm (Fin 2)) →ₗ[ℝ]
      CompactRealForm (Fin 6) where
  toFun := differentialValue
  map_add' := by
    intro A B
    apply CompactRealForm.ext
    apply Subtype.ext
    exact differentialMatrix_add A B
  map_smul' := by
    intro t A
    apply CompactRealForm.ext
    apply Subtype.ext
    exact differentialMatrix_smul t A

set_option linter.style.haveILetI false in
theorem embedding_oneParameter_hasRealDerivAt
    (X : CompactRealForm (Fin 3)) (Y : CompactRealForm (Fin 2)) :
    OneParameterSubgroup.HasRealDerivAt
      (fun t : ℝ =>
        ((embedding
          (CompactRealForm.expSpecialUnitary (t • X),
            CompactRealForm.expSpecialUnitary (t • Y)) : SU6) : Matrix6))
      (differential (X, Y) : Matrix6) 0 := by
  letI hNormedAdd3 : NormedAddCommGroup Matrix3 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix3 := hNormedAdd3.toAddCommGroup
  letI hNormedAdd2 : NormedAddCommGroup Matrix2 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix2 := hNormedAdd2.toAddCommGroup
  letI hNormedAdd6 : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAdd6.toAddCommGroup
  change HasDerivAt
    (fun t : ℝ =>
      ((embedding
        (CompactRealForm.expSpecialUnitary (t • X),
          CompactRealForm.expSpecialUnitary (t • Y)) : SU6) : Matrix6))
    (blockMatrix ((X : Matrix3), (Y : Matrix2))) 0
  have hColor : HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • (X : Matrix3)))
      (X : Matrix3) 0 := by
    simpa using hasDerivAt_exp_smul_const (X : Matrix3) (0 : ℝ)
  have hWeak : HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • (Y : Matrix2)))
      (Y : Matrix2) 0 := by
    simpa using hasDerivAt_exp_smul_const (Y : Matrix2) (0 : ℝ)
  have hPair := hColor.prodMk hWeak
  have hBlock : HasDerivAt
      (fun t : ℝ => blockMatrix
        (NormedSpace.exp (t • (X : Matrix3)),
          NormedSpace.exp (t • (Y : Matrix2))))
      (blockMatrix ((X : Matrix3), (Y : Matrix2))) 0 := by
    simpa [blockMatrixContinuousLinear, blockMatrixLinear,
      Function.comp_def] using
      blockMatrixContinuousLinear.hasFDerivAt.comp_hasDerivAt 0 hPair
  have hAffine := hBlock.add_const singletMatrix
  rw [hasDerivAt_iff_tendsto]
  have hTendsto := hasDerivAt_iff_tendsto.mp hAffine
  simpa only [embedding_coe, CompactRealForm.coe_expSpecialUnitary,
    CompactRealForm.coe_real_smul, real_smul_matrix_eq_complex_smul] using
    hTendsto

def oneParameterDifferentiable :
    OneParameterDifferentiableEmbedding embedding where
  differential := differential
  derivative_at_zero := embedding_oneParameter_hasRealDerivAt

def continuousOneParameterDifferentiable :
    OneParameterDifferentiableEmbedding
      (continuousEmbedding : ProductGroup →* SU6) :=
  oneParameterDifferentiable

end
end StandardSemisimpleEmbedding
end GUT
