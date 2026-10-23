import GUT.SU6.SelectionRules.StandardBranch.StandardBlockPhysicalCharacterBridge
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Physics

open Math

/-!
# Simultaneous standard coordinates for the actual compact centralizer

The semisimple embedding classification weak-doublet decomposition gives three pairwise orthogonal coordinate
subspaces of dimensions `3`, `2`, and `1`.  This file chooses orthonormal bases
in that fixed order and constructs one unitary change of basis from the
standard coordinates.  A one-column phase correction makes its determinant
one without changing its conjugation action on diagonal block scalars.
-/

namespace GUT
namespace ActualBlockConjugacy

open scoped BigOperators

open ActualBlockCentralizer
open ActualCompactCentralizer
open CompactEmbeddingClassification
open UnitarySubrepresentationOrthogonality
open StandardBlockPhysicalCharacterBridge

noncomputable section

/-- Semantic labels for the ordered actual semisimple embedding classification blocks. -/
inductive BlockLabel
  | color
  | weak
  | singlet
  deriving DecidableEq

/-- Enumeration of the three semantic blocks. -/
def blockLabelEquivFin3 : BlockLabel ≃ Fin 3 where
  toFun
    | .color => 0
    | .weak => 1
    | .singlet => 2
  invFun i :=
    if i = 0 then .color else if i = 1 then .weak else .singlet
  left_inv label := by
    cases label <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

instance : Fintype BlockLabel :=
  Fintype.ofEquiv (Fin 3) blockLabelEquivFin3.symm

namespace BlockLabel

/-- The dimensions of the color, weak, and singlet blocks. -/
def dimension : BlockLabel → ℕ
  | color => 3
  | weak => 2
  | singlet => 1

end BlockLabel

/-- The three coordinate ranges in the original Euclidean defining
representation. -/
def coordinateRange
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    BlockLabel → Submodule ℂ EuclideanRepSpace
  | .color => (colorCoordinateIntertwiner iota W).range.toSubmodule
  | .weak => (weakCoordinateIntertwiner iota W).range.toSubmodule
  | .singlet => (singletCoordinateIntertwiner iota W).range.toSubmodule

@[simp]
theorem coordinateRange_color
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    coordinateRange iota W .color =
      (colorCoordinateIntertwiner iota W).range.toSubmodule :=
  rfl

@[simp]
theorem coordinateRange_weak
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    coordinateRange iota W .weak =
      (weakCoordinateIntertwiner iota W).range.toSubmodule :=
  rfl

@[simp]
theorem coordinateRange_singlet
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    coordinateRange iota W .singlet =
      (singletCoordinateIntertwiner iota W).range.toSubmodule :=
  rfl

theorem coordinateRange_finrank
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (label : BlockLabel) :
    Module.finrank ℂ (coordinateRange iota W label) = label.dimension := by
  cases label with
  | color =>
      rw [coordinateRange_color,
        finrank_range_eq _ (colorCoordinateIntertwiner_injective iota W)]
      simp [ColorBlockSpace, BlockLabel.dimension]
  | weak =>
      rw [coordinateRange_weak,
        finrank_range_eq _ (weakCoordinateIntertwiner_injective iota W)]
      simp [WeakBlockSpace, BlockLabel.dimension]
  | singlet =>
      rw [coordinateRange_singlet,
        finrank_range_eq _ (singletCoordinateIntertwiner_injective iota W)]
      simp [SingletBlockSpace, BlockLabel.dimension]

/-- The actual coordinate ranges are pairwise orthogonal. -/
theorem coordinateRange_orthogonalFamily
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    OrthogonalFamily ℂ
      (fun label => coordinateRange iota W label)
      (fun label => (coordinateRange iota W label).subtypeₗᵢ) := by
  rw [orthogonalFamily_iff_pairwise]
  intro a b hab
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact colorRange_isOrtho_weakRange iota W
  · exact colorRange_isOrtho_singletRange iota W
  · exact (colorRange_isOrtho_weakRange iota W).symm
  · exact (hab rfl).elim
  · exact weakRange_isOrtho_singletRange iota W
  · exact (colorRange_isOrtho_singletRange iota W).symm
  · exact (weakRange_isOrtho_singletRange iota W).symm
  · exact (hab rfl).elim

/-- The three coordinate ranges span the original six-dimensional space. -/
theorem iSup_coordinateRange_eq_top
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    iSup (coordinateRange iota W) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [Submodule.mem_iSup]
  intro N hN
  have hColor : colorComponent iota W x ∈ N :=
    hN .color ⟨_, rfl⟩
  have hWeak : weakComponent iota W x ∈ N :=
    hN .weak ⟨_, rfl⟩
  have hSinglet : singletComponent iota W x ∈ N :=
    hN .singlet ⟨_, rfl⟩
  rw [← component_sum iota W x]
  exact N.add_mem (N.add_mem hColor hWeak) hSinglet

/-- The actual coordinate ranges form an internal orthogonal direct sum. -/
theorem coordinateRange_isInternal
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    DirectSum.IsInternal (coordinateRange iota W) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨(coordinateRange_orthogonalFamily iota W).independent,
    iSup_coordinateRange_eq_top iota W⟩

/-- A chosen orthonormal basis on each actual coordinate range, indexed by
its semantic dimension. -/
def coordinateRangeBasis
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (label : BlockLabel) :
    OrthonormalBasis (Fin label.dimension) ℂ (coordinateRange iota W label) :=
  (stdOrthonormalBasis ℂ (coordinateRange iota W label)).reindex
    (finCongr (coordinateRange_finrank iota W label))

/-- The disjoint union of the three ordered block bases. -/
def sigmaBlockBasis
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    OrthonormalBasis
      (Σ label : BlockLabel, Fin (BlockLabel.dimension label))
      ℂ EuclideanRepSpace :=
  (coordinateRange_isInternal iota W).collectedOrthonormalBasis
    (coordinateRange_orthogonalFamily iota W)
    (coordinateRangeBasis iota W)

theorem sigmaBlockBasis_mem
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (a : Σ label : BlockLabel, Fin (BlockLabel.dimension label)) :
    sigmaBlockBasis iota W a ∈ coordinateRange iota W a.1 := by
  exact (coordinateRange_isInternal iota W).collectedOrthonormalBasis_mem
    (coordinateRange_orthogonalFamily iota W)
    (coordinateRangeBasis iota W) a

/-- The dependent block index as the explicit ordered sum `3 + 2 + 1`. -/
def sigmaBlockEquivSum :
    (Σ label : BlockLabel, Fin (BlockLabel.dimension label)) ≃
      Fin 3 ⊕ (Fin 2 ⊕ Fin 1) where
  toFun a := by
    rcases a with ⟨label, i⟩
    cases label with
    | color => exact Sum.inl i
    | weak => exact Sum.inr (Sum.inl i)
    | singlet => exact Sum.inr (Sum.inr i)
  invFun a := by
    cases a with
    | inl i => exact ⟨.color, i⟩
    | inr a =>
        cases a with
        | inl i => exact ⟨.weak, i⟩
        | inr i => exact ⟨.singlet, i⟩
  left_inv a := by
    rcases a with ⟨label, i⟩
    cases label <;> rfl
  right_inv a := by
    rcases a with i | a
    · rfl
    · rcases a with i | i <;> rfl

/-- Ordered block indices identified with the six standard coordinates. -/
def blockIndexEquivFin6 :
    (Σ label : BlockLabel, Fin (BlockLabel.dimension label)) ≃ Fin 6 :=
  sigmaBlockEquivSum.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 3)) finSumFinEquiv).trans
      finSumFinEquiv)

@[simp]
theorem blockIndexEquivFin6_color (i : Fin 3) :
    blockIndexEquivFin6 ⟨.color, i⟩ = Fin.castAdd 3 i := by
  change finSumFinEquiv (Sum.inl i) = Fin.castAdd 3 i
  exact finSumFinEquiv_apply_left i

@[simp]
theorem blockIndexEquivFin6_weak (i : Fin 2) :
    blockIndexEquivFin6 ⟨.weak, i⟩ =
      Fin.natAdd 3 (Fin.castAdd 1 i) := by
  change
    finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i))) =
      Fin.natAdd 3 (Fin.castAdd 1 i)
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

@[simp]
theorem blockIndexEquivFin6_singlet (i : Fin 1) :
    blockIndexEquivFin6 ⟨.singlet, i⟩ =
      Fin.natAdd 3 (Fin.natAdd 2 i) := by
  change
    finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i))) =
      Fin.natAdd 3 (Fin.natAdd 2 i)
  rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right]

/-- An orthonormal basis of the original defining space whose first three
vectors are color, next two weak, and last one singlet. -/
def orderedBlockBasis
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    OrthonormalBasis (Fin 6) ℂ EuclideanRepSpace :=
  (sigmaBlockBasis iota W).reindex blockIndexEquivFin6

theorem orderedBlockBasis_apply_blockIndex
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (a : Σ label : BlockLabel, Fin (BlockLabel.dimension label)) :
    orderedBlockBasis iota W (blockIndexEquivFin6 a) =
      sigmaBlockBasis iota W a := by
  simp [orderedBlockBasis]

theorem orderedBlockBasis_mem_blockIndex
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (a : Σ label : BlockLabel, Fin (BlockLabel.dimension label)) :
    orderedBlockBasis iota W (blockIndexEquivFin6 a) ∈
      coordinateRange iota W a.1 := by
  rw [orderedBlockBasis_apply_blockIndex]
  exact sigmaBlockBasis_mem iota W a

/-!
## The two block-scalar actions in the ordered basis
-/

/-- The complex scalar attached to each semantic block. -/
def blockScalar (p : CompactBlockCentralizer.Group) : BlockLabel → ℂ
  | .color => (p.1.1 : ℂ)
  | .weak => (p.1.2.1 : ℂ)
  | .singlet => (p.1.2.2 : ℂ)

/-- The actual reconstructed centralizer matrix acts by the corresponding
scalar on every vector in a coordinate range. -/
theorem blockCoefficientMatrix_action_of_mem
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) (label : BlockLabel)
    (v : EuclideanRepSpace) (hv : v ∈ coordinateRange iota W label) :
    Matrix.toEuclideanLin (blockCoefficientMatrix iota W p.1) v =
      blockScalar p label • v := by
  rw [blockCoefficientMatrix_toEuclideanLin]
  rw [show
      (originalCircleLinearIsometryEquiv iota W p.1).toLinearEquiv.toLinearMap =
        (originalCircleIntertwiner iota W p.1).toLinearMap by
    exact originalCircleLinearEquiv_toLinearMap iota W p.1]
  cases label with
  | color =>
      rcases hv with ⟨x, rfl⟩
      simp [originalCircleIntertwiner, orderedBlockScalarIntertwiner,
        orderedBlockScalarLinearMap, blockScalar]
      rw [← map_smul]
      congr 1
      simp
  | weak =>
      rcases hv with ⟨x, rfl⟩
      simp [originalCircleIntertwiner, orderedBlockScalarIntertwiner,
        orderedBlockScalarLinearMap, blockScalar]
      rw [← map_smul]
      congr 1
      simp
  | singlet =>
      rcases hv with ⟨x, rfl⟩
      simp [originalCircleIntertwiner, orderedBlockScalarIntertwiner,
        orderedBlockScalarLinearMap, blockScalar]
      rw [← map_smul]
      congr 1
      simp

/-- The standard diagonal block torus has the same scalar at the standard
coordinate assigned to each actual block-basis vector. -/
theorem ambientBlock_coords_blockIndex
    (p : CompactBlockCentralizer.Group)
    (a : Σ label : BlockLabel, Fin (BlockLabel.dimension label)) :
    AmbientTorus.coords
        (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)
        (blockIndexEquivFin6 a) =
      blockScalar p a.1 := by
  rcases a with ⟨label, i⟩
  cases label with
  | color =>
      simp only [BlockLabel.dimension] at i ⊢
      change
        AmbientTorus.coords
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)
            (Fin.castAdd 3 i) = (p.1.1 : ℂ)
      fin_cases i <;> rfl
  | weak =>
      simp only [BlockLabel.dimension] at i ⊢
      change
        AmbientTorus.coords
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)
            (Fin.natAdd 3 (Fin.castAdd 1 i)) = (p.1.2.1 : ℂ)
      fin_cases i <;> rfl
  | singlet =>
      simp only [BlockLabel.dimension] at i ⊢
      change
        AmbientTorus.coords
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)
            (Fin.natAdd 3 (Fin.natAdd 2 i)) = (p.1.2.2 : ℂ)
      have hi : Fin.natAdd 3 (Fin.natAdd 2 i) = Fin.last 5 := by
        have hzero : i = 0 := Fin.eq_zero i
        subst i
        rfl
      rw [hi, AmbientTorus.coords_last]
      have hprod :
          (∏ j : Fin 5,
            StandardBlockPhysicalCharacterBridge.blockAmbientHom p j) =
            p.1.1 ^ 3 * p.1.2.1 ^ 2 := by
        simp [StandardBlockPhysicalCharacterBridge.blockAmbientHom,
          Fin.prod_univ_succ, pow_succ]
        ac_rfl
      rw [hprod]
      change
        (((p.1.1 ^ 3 * p.1.2.1 ^ 2)⁻¹ : Circle) : ℂ) =
          (p.1.2.2 : ℂ)
      have hp := p.property
      change p.1.1 ^ 3 * p.1.2.1 ^ 2 * p.1.2.2 = 1 at hp
      exact congrArg (fun z : Circle => (z : ℂ))
        ((inv_eq_iff_mul_eq_one).2 hp)

/-!
## A common unitary intertwiner
-/

/-- The unitary map sending the standard basis to the ordered actual block
basis. -/
def orderedBasisIsometry
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    EuclideanRepSpace ≃ₗᵢ[ℂ] EuclideanRepSpace :=
  (EuclideanSpace.basisFun (Fin 6) ℂ).equiv
    (orderedBlockBasis iota W) (Equiv.refl (Fin 6))

theorem orderedBasisIsometry_apply_blockIndex
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (a : Σ label : BlockLabel, Fin (BlockLabel.dimension label)) :
    orderedBasisIsometry iota W
        (EuclideanSpace.basisFun (Fin 6) ℂ (blockIndexEquivFin6 a)) =
      sigmaBlockBasis iota W a := by
  rw [orderedBasisIsometry, OrthonormalBasis.equiv_apply_basis]
  exact orderedBlockBasis_apply_blockIndex iota W a

/-- The matrix of the common unitary basis change in standard coordinates. -/
def orderedBasisMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (orderedBasisIsometry iota W).toLinearEquiv.toLinearMap

theorem orderedBasisMatrix_toEuclideanLin
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Matrix.toEuclideanLin (orderedBasisMatrix iota W) =
      (orderedBasisIsometry iota W).toLinearEquiv.toLinearMap := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_toMatrix _ _ _

theorem orderedBasisMatrix_mem_unitaryGroup
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    orderedBasisMatrix iota W ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  exact (orderedBasisIsometry iota W).toMatrix_mem_unitaryGroup
    (EuclideanSpace.basisFun (Fin 6) ℂ)
    (EuclideanSpace.basisFun (Fin 6) ℂ)

/-- The standard diagonal block matrix acts on its assigned standard basis
vector by the same scalar as the actual block matrix. -/
theorem diagonalBlock_action_standardBasis
    (p : CompactBlockCentralizer.Group)
    (a : Σ label : BlockLabel, Fin (BlockLabel.dimension label)) :
    Matrix.toEuclideanLin
        (((AmbientTorus.toSU6MonoidHom
          (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
            Matrix (Fin 6) (Fin 6) ℂ))
        (EuclideanSpace.basisFun (Fin 6) ℂ (blockIndexEquivFin6 a)) =
      blockScalar p a.1 •
        EuclideanSpace.basisFun (Fin 6) ℂ (blockIndexEquivFin6 a) := by
  change
    Matrix.toEuclideanLin
        (Matrix.diagonal
          (AmbientTorus.coords
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)))
        (EuclideanSpace.basisFun (Fin 6) ℂ (blockIndexEquivFin6 a)) = _
  simp only [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply,
    PiLp.ofLp_single, Matrix.diagonal_mulVec_single,
    ambientBlock_coords_blockIndex]
  apply PiLp.ext
  intro j
  simp [PiLp.smul_apply, PiLp.single_apply, Pi.single_apply]

/-- The actual block-scalar matrix and the standard diagonal block matrix
are intertwined by the one common ordered basis change. -/
theorem blockCoefficientMatrix_mul_orderedBasisMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    blockCoefficientMatrix iota W p.1 * orderedBasisMatrix iota W =
      orderedBasisMatrix iota W *
        (((AmbientTorus.toSU6MonoidHom
          (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
            Matrix (Fin 6) (Fin 6) ℂ)) := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same,
    orderedBasisMatrix_toEuclideanLin]
  apply (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis.ext
  intro j
  obtain ⟨a, rfl⟩ := blockIndexEquivFin6.surjective j
  change
    Matrix.toEuclideanLin (blockCoefficientMatrix iota W p.1)
        (orderedBasisIsometry iota W
          (EuclideanSpace.basisFun (Fin 6) ℂ (blockIndexEquivFin6 a))) =
      orderedBasisIsometry iota W
        (Matrix.toEuclideanLin
          (((AmbientTorus.toSU6MonoidHom
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
              Matrix (Fin 6) (Fin 6) ℂ))
          (EuclideanSpace.basisFun (Fin 6) ℂ (blockIndexEquivFin6 a)))
  rw [orderedBasisIsometry_apply_blockIndex,
    diagonalBlock_action_standardBasis, map_smul,
    orderedBasisIsometry_apply_blockIndex]
  exact blockCoefficientMatrix_action_of_mem iota W p a.1 _
    (sigmaBlockBasis_mem iota W a)

/-!
## Determinant correction
-/

/-- The determinant of the ordered unitary basis matrix, bundled as a
unitary scalar. -/
def orderedBasisDetUnitary
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    unitary ℂ :=
  ⟨Matrix.det (orderedBasisMatrix iota W),
    Matrix.det_of_mem_unitary (orderedBasisMatrix_mem_unitaryGroup iota W)⟩

/-- Correct the determinant in the first color coordinate only. -/
def determinantCorrectionCoords
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) : Fin 6 → ℂ :=
  fun i =>
    if i = 0 then (((orderedBasisDetUnitary iota W)⁻¹ : unitary ℂ) : ℂ)
    else 1

def determinantCorrectionMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (determinantCorrectionCoords iota W)

theorem determinantCorrectionMatrix_mem_unitaryGroup
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    determinantCorrectionMatrix iota W ∈
      Matrix.unitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, determinantCorrectionMatrix,
    Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply, Matrix.one_apply, ite_eq_left]
    by_cases hi : i = 0
    · subst i
      exact (orderedBasisDetUnitary iota W)⁻¹ |>.property.2
    · simp [determinantCorrectionCoords, hi]
  · simp [hij]

theorem determinantCorrectionMatrix_det
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Matrix.det (determinantCorrectionMatrix iota W) =
      (Matrix.det (orderedBasisMatrix iota W))⁻¹ := by
  rw [determinantCorrectionMatrix, Matrix.det_diagonal,
    Fin.prod_univ_succ]
  simp [determinantCorrectionCoords, orderedBasisDetUnitary]
  exact Unitary.coe_inv (orderedBasisDetUnitary iota W)

/-- The determinant-corrected common basis matrix. -/
def specialOrderedBasisMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  orderedBasisMatrix iota W * determinantCorrectionMatrix iota W

theorem specialOrderedBasisMatrix_mem_unitaryGroup
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    specialOrderedBasisMatrix iota W ∈
      Matrix.unitaryGroup (Fin 6) ℂ := by
  exact (Matrix.unitaryGroup (Fin 6) ℂ).mul_mem
    (orderedBasisMatrix_mem_unitaryGroup iota W)
    (determinantCorrectionMatrix_mem_unitaryGroup iota W)

theorem specialOrderedBasisMatrix_det
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Matrix.det (specialOrderedBasisMatrix iota W) = 1 := by
  rw [specialOrderedBasisMatrix, Matrix.det_mul,
    determinantCorrectionMatrix_det]
  have hdet : Matrix.det (orderedBasisMatrix iota W) ≠ 0 := by
    intro hzero
    have hunit := (orderedBasisDetUnitary iota W).property.1
    change star (Matrix.det (orderedBasisMatrix iota W)) *
        Matrix.det (orderedBasisMatrix iota W) = 1 at hunit
    rw [hzero, mul_zero] at hunit
    exact zero_ne_one hunit
  exact mul_inv_cancel₀ hdet

/-- The common ordered basis change as an element of `SU(6)`. -/
def standardizingConjugator
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) : SU6 :=
  ⟨specialOrderedBasisMatrix iota W, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨specialOrderedBasisMatrix_mem_unitaryGroup iota W,
      specialOrderedBasisMatrix_det iota W⟩⟩

/-- The determinant correction commutes with every standard diagonal block
matrix. -/
theorem determinantCorrectionMatrix_commutes_diagonalBlock
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    determinantCorrectionMatrix iota W *
        (((AmbientTorus.toSU6MonoidHom
          (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
            Matrix (Fin 6) (Fin 6) ℂ)) =
      (((AmbientTorus.toSU6MonoidHom
          (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
            Matrix (Fin 6) (Fin 6) ℂ)) *
        determinantCorrectionMatrix iota W := by
  change
    Matrix.diagonal (determinantCorrectionCoords iota W) *
        Matrix.diagonal
          (AmbientTorus.coords
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)) =
      Matrix.diagonal
          (AmbientTorus.coords
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)) *
        Matrix.diagonal (determinantCorrectionCoords iota W)
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  exact mul_comm _ _

/-- The determinant-corrected `SU(6)` basis change still intertwines every
actual block coefficient matrix with its standard diagonal form. -/
theorem blockCoefficientMatrix_mul_specialOrderedBasisMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    blockCoefficientMatrix iota W p.1 * specialOrderedBasisMatrix iota W =
      specialOrderedBasisMatrix iota W *
        (((AmbientTorus.toSU6MonoidHom
          (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
            Matrix (Fin 6) (Fin 6) ℂ)) := by
  rw [specialOrderedBasisMatrix]
  calc
    blockCoefficientMatrix iota W p.1 *
          (orderedBasisMatrix iota W * determinantCorrectionMatrix iota W) =
        (blockCoefficientMatrix iota W p.1 * orderedBasisMatrix iota W) *
          determinantCorrectionMatrix iota W := by rw [Matrix.mul_assoc]
    _ = (orderedBasisMatrix iota W *
          (((AmbientTorus.toSU6MonoidHom
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
              Matrix (Fin 6) (Fin 6) ℂ))) *
          determinantCorrectionMatrix iota W := by
      rw [blockCoefficientMatrix_mul_orderedBasisMatrix]
    _ = orderedBasisMatrix iota W *
          ((((AmbientTorus.toSU6MonoidHom
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
              Matrix (Fin 6) (Fin 6) ℂ)) *
            determinantCorrectionMatrix iota W) := by rw [Matrix.mul_assoc]
    _ = orderedBasisMatrix iota W *
          (determinantCorrectionMatrix iota W *
            (((AmbientTorus.toSU6MonoidHom
              (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
                Matrix (Fin 6) (Fin 6) ℂ))) := by
      rw [determinantCorrectionMatrix_commutes_diagonalBlock]
    _ = (orderedBasisMatrix iota W * determinantCorrectionMatrix iota W) *
          (((AmbientTorus.toSU6MonoidHom
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) : SU6) :
              Matrix (Fin 6) (Fin 6) ℂ)) := by rw [Matrix.mul_assoc]

/-!
## Simultaneous conjugacy and the standard charge-orbit bridge certificate
-/

/-- One fixed special-unitary matrix simultaneously conjugates every
standard block-torus point to the corresponding actual centralizer point. -/
theorem blockCoefficientSU6_eq_conjugate
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    blockCoefficientSU6 iota W p =
      standardizingConjugator iota W *
        AmbientTorus.toSU6MonoidHom
          (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) *
        (standardizingConjugator iota W)⁻¹ := by
  have hIntertwine :
      blockCoefficientSU6 iota W p * standardizingConjugator iota W =
        standardizingConjugator iota W *
          AmbientTorus.toSU6MonoidHom
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p) := by
    apply Subtype.ext
    exact blockCoefficientMatrix_mul_specialOrderedBasisMatrix iota W p
  calc
    blockCoefficientSU6 iota W p =
        blockCoefficientSU6 iota W p *
          (standardizingConjugator iota W *
            (standardizingConjugator iota W)⁻¹) := by simp
    _ = (blockCoefficientSU6 iota W p *
          standardizingConjugator iota W) *
            (standardizingConjugator iota W)⁻¹ := by rw [mul_assoc]
    _ = (standardizingConjugator iota W *
          AmbientTorus.toSU6MonoidHom
            (StandardBlockPhysicalCharacterBridge.blockAmbientHom p)) *
            (standardizingConjugator iota W)⁻¹ := by rw [hIntertwine]

/-- Extracting the compact block coefficients of an actual centralizer
element and reconstructing them recovers that element. -/
theorem centralizerElement_eq_blockCoefficientSU6
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    U.1 = blockCoefficientSU6 iota W
      (compactBlockCoefficients iota W U) := by
  let p := compactBlockCoefficients iota W U
  have hRecover :
      U = reconstructedCentralizerElement iota W p := by
    apply compactBlockCoefficientHom_injective iota W
    change compactBlockCoefficients iota W U =
      compactBlockCoefficients iota W
        (reconstructedCentralizerElement iota W p)
    rw [compactBlockCoefficients_reconstructed]
  exact congrArg Subtype.val hRecover

/-- Any supplied centralizing gauge lift is exactly the reconstructed actual
block coefficient lift. -/
theorem gauge_eq_blockCoefficientSU6
    {H : Type*} [CommGroup H]
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (h : H) :
    gauge h = blockCoefficientSU6 iota W
      (StandardBlockGaugeCancellation.actualBlockGaugeHom
        iota W gauge hCentral h) := by
  change gauge h = blockCoefficientSU6 iota W
    (compactBlockCoefficients iota W
      (⟨gauge h, hCentral h⟩ : PhysicalCentralizer iota))
  exact centralizerElement_eq_blockCoefficientSU6 iota W
    (⟨gauge h, hCentral h⟩ : PhysicalCentralizer iota)

/-- The semisimple embedding classification weak-doublet decomposition itself supplies the standardizing
conjugator required by the physical trace bridge. -/
def actualBlockDiagonalization
    {H : Type*} [CommGroup H]
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota) :
    StandardBlockPhysicalCharacterBridge.ActualBlockDiagonalization
      H iota W gauge hCentral where
  conjugator := standardizingConjugator iota W
  gauge_eq h := by
    rw [gauge_eq_blockCoefficientSU6 iota W gauge hCentral h]
    exact blockCoefficientSU6_eq_conjugate iota W
      (StandardBlockGaugeCancellation.actualBlockGaugeHom
        iota W gauge hCentral h)

universe u

variable {H : Type u} [CommGroup H]

/-- Promote a raw projected physical source to the trace-interpreted source;
no additional conjugacy certificate is required. -/
def projectedSourceToTraceSource
    (S : StandardBlockChargeProjection.PureSMActualBlockProjectedSource H) :
    StandardBlockPhysicalCharacterBridge.PureSMActualBlockTraceSource H where
  toProjected := S
  diagonalization := actualBlockDiagonalization S.iota S.weakDoubletData
    S.gauge S.gauge_centralizes

/-- The physical virtual trace of every projected source is therefore the
canonical exact-SM-plus-singlets character target. -/
theorem physicalTrace_eq_exactSMTarget
    (S : StandardBlockChargeProjection.PureSMActualBlockProjectedSource H)
    (h : H) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        (StandardBlockPhysicalCharacterBridge.CommonGaugeSource.physicalVirtualRepresentation
          S.matter) h =
      StandardSMCharacterTarget.eval
        (StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter
          S.generations S.physicalCharges S.singlets) 0 h :=
  (projectedSourceToTraceSource S).physicalTrace_eq_exactSMTarget h

/-- For a strict ordinary Abelian source, the actual residual-action trace is
the charge-resolved character constructed from its simultaneous eigenspaces.
The identity gauge lift and its centralizer property are canonical. -/
theorem ordinaryAbelianPhysicalTrace_eq_resolvedCharacter
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (source : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (h : H) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        (StandardBlockPhysicalCharacterBridge.OrdinaryAbelianSource.physicalVirtualRepresentation
          source) h =
      StandardSMCharacterTarget.eval
        (StandardBlockChargeProjection.ordinaryAbelianResolvedCharacter
          iota W source) 0 h :=
  StandardBlockPhysicalCharacterBridge.OrdinaryAbelianSource.physicalVirtualRepresentation_character_eq_ordinaryAbelianResolved
      (actualBlockDiagonalization iota W
        (1 : H →* SU6)
        (StandardBlockChargeProjection.identityGauge_centralizes iota))
      source h

/-- The exact local SM coefficient certificate therefore identifies the
trace of the originally supplied ordinary Abelian actions with the canonical
SM-plus-singlets target. -/
theorem ordinaryAbelianPhysicalTrace_eq_exactSMTarget
    {H : Type u} [CommGroup H]
    (S : StandardBlockChargeProjection.PureSMOrdinaryAbelianProjectedSource H)
    (h : H) :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character
        (StandardBlockPhysicalCharacterBridge.OrdinaryAbelianSource.physicalVirtualRepresentation
          S.matter) h =
      StandardSMCharacterTarget.eval
        (StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter
          S.generations S.physicalCharges S.singlets) 0 h := by
  rw [ordinaryAbelianPhysicalTrace_eq_resolvedCharacter
    S.iota S.weakDoubletData S.matter h,
    S.spectrum.resolvedCharacter_eq]

end

end ActualBlockConjugacy
end GUT
