import GUT.SU6.Hypercharge.ActualCompactCentralizer
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reconstructing the actual compact centralizer

This file proves the converse to the coefficient map constructed in
`ActualCompactCentralizer`.  Circle-valued coefficients act on the three
actual irreducible constituents.  Orthogonality of those constituents makes
the resulting operator unitary on the original Euclidean representation.
-/

namespace GUT
namespace ActualCompactCentralizer

open WeakDoubletEmbeddingClassification
open CompactEmbeddingClassification
open ActualBlockCentralizer

noncomputable section

/-!
## Orthogonal components in the original representation
-/

/-- The color component of a vector, embedded back into the original
Euclidean representation. -/
def colorComponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : EuclideanRepSpace) : EuclideanRepSpace :=
  colorCoordinateIntertwiner iota W
    ((representationEquivOrderedBlocks W x).1)

/-- The weak component of a vector in the original representation. -/
def weakComponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : EuclideanRepSpace) : EuclideanRepSpace :=
  weakCoordinateIntertwiner iota W
    ((representationEquivOrderedBlocks W x).2.1)

/-- The singlet component of a vector in the original representation. -/
def singletComponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : EuclideanRepSpace) : EuclideanRepSpace :=
  singletCoordinateIntertwiner iota W
    ((representationEquivOrderedBlocks W x).2.2)

/-- The three coordinate components sum to the original vector. -/
theorem component_sum
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : EuclideanRepSpace) :
    colorComponent iota W x + weakComponent iota W x +
        singletComponent iota W x = x := by
  apply (representationEquivOrderedBlocks W).injective
  simp [colorComponent, weakComponent, singletComponent]

theorem colorComponent_inner_weakComponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x y : EuclideanRepSpace) :
    inner ℂ (colorComponent iota W x) (weakComponent iota W y) = 0 := by
  exact (colorRange_isOrtho_weakRange iota W).inner_eq
    ⟨_, rfl⟩ ⟨_, rfl⟩

theorem colorComponent_inner_singletComponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x y : EuclideanRepSpace) :
    inner ℂ (colorComponent iota W x) (singletComponent iota W y) = 0 := by
  exact (colorRange_isOrtho_singletRange iota W).inner_eq
    ⟨_, rfl⟩ ⟨_, rfl⟩

theorem weakComponent_inner_singletComponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x y : EuclideanRepSpace) :
    inner ℂ (weakComponent iota W x) (singletComponent iota W y) = 0 := by
  exact (weakRange_isOrtho_singletRange iota W).inner_eq
    ⟨_, rfl⟩ ⟨_, rfl⟩

/-!
## Circle-scalar action
-/

/-- Multiplication by a unit-circle scalar as a complex-linear
automorphism. -/
def circleScalarLinearEquiv (z : Circle) (V : Type*)
    [AddCommMonoid V] [Module ℂ V] : V ≃ₗ[ℂ] V :=
  DistribMulAction.toLinearEquiv ℂ V z

@[simp]
theorem circleScalarLinearEquiv_apply (z : Circle) (V : Type*)
    [AddCommMonoid V] [Module ℂ V] (x : V) :
    circleScalarLinearEquiv z V x = (z : ℂ) • x := by
  change z • x = (z : ℂ) • x
  rfl

/-- Coefficientwise circle-scalar multiplication on the ordered three-block
space. -/
def orderedCircleLinearEquiv
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    OrderedBlockSpace W ≃ₗ[ℂ] OrderedBlockSpace W :=
  LinearEquiv.prodCongr
    (circleScalarLinearEquiv p.1 (ColorBlockSpace W))
    (LinearEquiv.prodCongr
      (circleScalarLinearEquiv p.2.1 (WeakBlockSpace W))
      (circleScalarLinearEquiv p.2.2 (SingletBlockSpace W)))

/-- The coefficientwise action conjugated back to the original Euclidean
representation. -/
def originalCircleLinearEquiv
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    EuclideanRepSpace ≃ₗ[ℂ] EuclideanRepSpace :=
  ((representationEquivOrderedBlocks W).toLinearEquiv.trans
    (orderedCircleLinearEquiv iota W p)).trans
    (representationEquivOrderedBlocks W).symm.toLinearEquiv

@[simp]
theorem originalCircleLinearEquiv_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients)
    (x : EuclideanRepSpace) :
    originalCircleLinearEquiv iota W p x =
      (p.1 : ℂ) • colorComponent iota W x +
        (p.2.1 : ℂ) • weakComponent iota W x +
        (p.2.2 : ℂ) • singletComponent iota W x := by
  apply (representationEquivOrderedBlocks W).injective
  simp [originalCircleLinearEquiv, orderedCircleLinearEquiv,
    colorComponent, weakComponent, singletComponent]

/-- Simultaneous multiplication by a unit-circle scalar preserves the inner
product. -/
theorem circle_inner (z : Circle) (x y : EuclideanRepSpace) :
    inner ℂ ((z : ℂ) • x) ((z : ℂ) • y) = inner ℂ x y := by
  rw [inner_smul_left, inner_smul_right]
  rw [← Circle.coe_inv_eq_conj]
  simp

/-- The reconstructed three-block action preserves the Euclidean inner
product. -/
theorem originalCircleLinearEquiv_inner_map_map
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients)
    (x y : EuclideanRepSpace) :
    inner ℂ (originalCircleLinearEquiv iota W p x)
        (originalCircleLinearEquiv iota W p y) = inner ℂ x y := by
  rw [originalCircleLinearEquiv_apply, originalCircleLinearEquiv_apply]
  calc
    _ = inner ℂ
        (colorComponent iota W x + weakComponent iota W x +
          singletComponent iota W x)
        (colorComponent iota W y + weakComponent iota W y +
          singletComponent iota W y) := by
      simp only [inner_add_left, inner_add_right]
      rw [circle_inner, circle_inner, circle_inner]
      simp [inner_smul_left, inner_smul_right,
        colorComponent_inner_weakComponent,
        colorComponent_inner_singletComponent,
        weakComponent_inner_singletComponent,
        inner_eq_zero_symm.mpr
          (colorComponent_inner_weakComponent iota W y x),
        inner_eq_zero_symm.mpr
          (colorComponent_inner_singletComponent iota W y x),
        inner_eq_zero_symm.mpr
          (weakComponent_inner_singletComponent iota W y x)]
    _ = inner ℂ x y := by
      rw [component_sum, component_sum]

/-- The reconstructed action as a unitary linear equivalence. -/
def originalCircleLinearIsometryEquiv
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    EuclideanRepSpace ≃ₗᵢ[ℂ] EuclideanRepSpace :=
  (originalCircleLinearEquiv iota W p).isometryOfInner
    (originalCircleLinearEquiv_inner_map_map iota W p)

@[simp]
theorem originalCircleLinearIsometryEquiv_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients)
    (x : EuclideanRepSpace) :
    originalCircleLinearIsometryEquiv iota W p x =
      originalCircleLinearEquiv iota W p x :=
  rfl

/-!
## Matrix reconstruction
-/

/-- The reconstructed action also intertwines the original restricted
representation with itself. -/
def originalCircleIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    Representation.IntertwiningMap
      (euclideanDefiningRestriction iota)
      (euclideanDefiningRestriction iota) :=
  (representationEquivOrderedBlocks W).symm.toIntertwiningMap.comp
    ((orderedBlockScalarIntertwiner W
      (p.1 : ℂ) (p.2.1 : ℂ) (p.2.2 : ℂ)).comp
      (representationEquivOrderedBlocks W).toIntertwiningMap)

theorem originalCircleLinearEquiv_toLinearMap
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    (originalCircleLinearEquiv iota W p).toLinearMap =
      (originalCircleIntertwiner iota W p).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (representationEquivOrderedBlocks W).injective
  simp [originalCircleLinearEquiv, orderedCircleLinearEquiv,
    originalCircleIntertwiner, orderedBlockScalarIntertwiner,
    orderedBlockScalarLinearMap]

/-- The matrix of the reconstructed unitary action in the standard
orthonormal basis of `EuclideanRepSpace`. -/
def blockCoefficientMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (originalCircleLinearIsometryEquiv iota W p).toLinearEquiv.toLinearMap

theorem blockCoefficientMatrix_toEuclideanLin
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    Matrix.toEuclideanLin (blockCoefficientMatrix iota W p) =
      (originalCircleLinearIsometryEquiv iota W p).toLinearEquiv.toLinearMap := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_toMatrix _ _ _

/-- The reconstructed coefficient matrix is unitary. -/
theorem blockCoefficientMatrix_mem_unitaryGroup
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    blockCoefficientMatrix iota W p ∈ Matrix.unitaryGroup (Fin 6) ℂ := by
  exact (originalCircleLinearIsometryEquiv iota W p).toMatrix_mem_unitaryGroup
    (EuclideanSpace.basisFun (Fin 6) ℂ)
    (EuclideanSpace.basisFun (Fin 6) ℂ)

/-- The determinant of the reconstructed matrix is the expected block
determinant. -/
theorem blockCoefficientMatrix_det
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.BlockCoefficients) :
    Matrix.det (blockCoefficientMatrix iota W p) =
      (p.1 : ℂ) ^ 3 * (p.2.1 : ℂ) ^ 2 * (p.2.2 : ℂ) := by
  rw [← LinearMap.det_toLpLin (p := 2)]
  change LinearMap.det
      (Matrix.toEuclideanLin (blockCoefficientMatrix iota W p)) = _
  rw [blockCoefficientMatrix_toEuclideanLin]
  rw [show
      (originalCircleLinearIsometryEquiv iota W p).toLinearEquiv.toLinearMap =
        (originalCircleIntertwiner iota W p).toLinearMap by
    exact originalCircleLinearEquiv_toLinearMap iota W p]
  rw [originalCircleIntertwiner]
  simp only [Representation.IntertwiningMap.comp_toLinearMap]
  have hConj := LinearMap.det_conj
    (orderedBlockScalarIntertwiner W
      (p.1 : ℂ) (p.2.1 : ℂ) (p.2.2 : ℂ)).toLinearMap
    (representationEquivOrderedBlocks W).toLinearEquiv.symm
  calc
    _ = LinearMap.det
        (orderedBlockScalarIntertwiner W
          (p.1 : ℂ) (p.2.1 : ℂ) (p.2.2 : ℂ)).toLinearMap := by
      convert hConj using 1
      simp only [Representation.Equiv.toLinearMap_symm]
      congr 1
    _ = _ := det_orderedBlockScalarLinearMap W _ _ _

/-- The kernel equation on compact coefficients makes the reconstructed
matrix special unitary. -/
theorem blockCoefficientMatrix_det_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    Matrix.det (blockCoefficientMatrix iota W p.1) = 1 := by
  rw [blockCoefficientMatrix_det]
  have hp := congrArg (fun z : Circle ↦ (z : ℂ)) p.property
  change
    (p.1.1 : ℂ) ^ 3 * (p.1.2.1 : ℂ) ^ 2 * (p.1.2.2 : ℂ) = 1
      at hp
  exact hp

/-- A determinant-one compact coefficient triple reconstructed as an actual
element of `SU(6)`. -/
def blockCoefficientSU6
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) : SU6 :=
  ⟨blockCoefficientMatrix iota W p.1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨blockCoefficientMatrix_mem_unitaryGroup iota W p.1,
      blockCoefficientMatrix_det_one iota W p⟩⟩

/-- The reconstructed special-unitary matrix commutes with the image of the
proposed semisimple embedding. -/
theorem blockCoefficientSU6_commutes
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) (g : ProductGroup) :
    blockCoefficientSU6 iota W p * iota g =
      iota g * blockCoefficientSU6 iota W p := by
  apply Subtype.ext
  apply Matrix.toEuclideanLin.injective
  change Matrix.toEuclideanLin
      (blockCoefficientMatrix iota W p.1 *
        (((iota g : SU6) : Matrix (Fin 6) (Fin 6) ℂ))) =
    Matrix.toEuclideanLin
      ((((iota g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) *
        blockCoefficientMatrix iota W p.1)
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same,
    blockCoefficientMatrix_toEuclideanLin]
  rw [show
      (originalCircleLinearIsometryEquiv iota W p.1).toLinearEquiv.toLinearMap =
        (originalCircleIntertwiner iota W p.1).toLinearMap by
    exact originalCircleLinearEquiv_toLinearMap iota W p.1]
  exact (originalCircleIntertwiner iota W p.1).isIntertwining' g

/-- The inverse construction from compact block coefficients to the actual
physical centralizer. -/
def reconstructedCentralizerElement
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) : PhysicalCentralizer iota :=
  ⟨blockCoefficientSU6 iota W p, by
    rw [Subgroup.mem_centralizer_iff]
    intro A hA
    rcases hA with ⟨g, rfl⟩
    exact (blockCoefficientSU6_commutes iota W p g).symm⟩

/-!
## Recovery of coefficients and the group equivalence
-/

theorem centralizerIntertwiner_reconstructed
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    centralizerIntertwiner iota (reconstructedCentralizerElement iota W p) =
      originalCircleIntertwiner iota W p.1 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change Matrix.toEuclideanLin (blockCoefficientMatrix iota W p.1) x = _
  rw [blockCoefficientMatrix_toEuclideanLin]
  rw [show
      (originalCircleLinearIsometryEquiv iota W p.1).toLinearEquiv.toLinearMap =
        (originalCircleIntertwiner iota W p.1).toLinearMap by
    exact originalCircleLinearEquiv_toLinearMap iota W p.1]

theorem transportedCentralizerIntertwiner_reconstructed
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    transportedCentralizerIntertwiner iota W
        (reconstructedCentralizerElement iota W p) =
      orderedBlockScalarIntertwiner W
        (p.1.1 : ℂ) (p.1.2.1 : ℂ) (p.1.2.2 : ℂ) := by
  rw [transportedCentralizerIntertwiner,
    centralizerIntertwiner_reconstructed]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp [BlockCentralizer.transportCommutant_apply,
    originalCircleIntertwiner]

theorem complexBlockCoefficients_reconstructed
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    complexBlockCoefficients iota W
        (reconstructedCentralizerElement iota W p) =
      ((p.1.1 : ℂ), ((p.1.2.1 : ℂ), (p.1.2.2 : ℂ))) := by
  apply complexBlockCoefficients_eq_of_spec
  exact transportedCentralizerIntertwiner_reconstructed iota W p

/-- Reconstructing a centralizer element and extracting its compact block
coefficients gives the original coefficient triple. -/
theorem compactBlockCoefficients_reconstructed
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : CompactBlockCentralizer.Group) :
    compactBlockCoefficients iota W
        (reconstructedCentralizerElement iota W p) = p := by
  have h := complexBlockCoefficients_reconstructed iota W p
  apply Subtype.ext
  apply Prod.ext
  · apply Circle.ext
    exact congrArg Prod.fst h
  · apply Prod.ext
    · apply Circle.ext
      exact congrArg (fun q : ℂ × (ℂ × ℂ) ↦ q.2.1) h
    · apply Circle.ext
      exact congrArg (fun q : ℂ × (ℂ × ℂ) ↦ q.2.2) h

/-- Every determinant-one compact block coefficient triple is realized by
an actual element of the `SU(6)` centralizer. -/
theorem compactBlockCoefficientHom_surjective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Surjective (compactBlockCoefficientHom iota W) := by
  intro p
  exact ⟨reconstructedCentralizerElement iota W p,
    compactBlockCoefficients_reconstructed iota W p⟩

/-- The actual centralizer is the compact determinant-one block coefficient
group. -/
def physicalCentralizerMulEquivCompactBlock
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    PhysicalCentralizer iota ≃* CompactBlockCentralizer.Group :=
  MulEquiv.ofBijective (compactBlockCoefficientHom iota W)
    ⟨compactBlockCoefficientHom_injective iota W,
      compactBlockCoefficientHom_surjective iota W⟩

/-- Consequently the actual centralizer is, as an abstract group, a
two-torus. -/
def physicalCentralizerMulEquivTorus
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    PhysicalCentralizer iota ≃* Circle × Circle :=
  (physicalCentralizerMulEquivCompactBlock iota W).trans
    CompactBlockCentralizer.torusMulEquiv.symm

end

end ActualCompactCentralizer
end GUT
