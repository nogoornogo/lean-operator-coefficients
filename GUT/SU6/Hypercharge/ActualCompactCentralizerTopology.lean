import GUT.SU6.Hypercharge.ActualCompactCentralizerEquivalence

/-!
# Topology of the actual compact centralizer

The explicit reconstruction from compact block coefficients is continuous.
Since its domain is compact and the actual matrix centralizer is Hausdorff,
its inverse is continuous as well.  This upgrades the abstract group
equivalence to a continuous group equivalence with the two-torus.
-/

namespace GUT
namespace ActualCompactCentralizer

open WeakDoubletEmbeddingClassification
open CompactEmbeddingClassification
open ActualBlockCentralizer

noncomputable section

/-- The reconstructed standard-basis matrix depends continuously on its
three circle coefficients. -/
theorem continuous_blockCoefficientMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Continuous (fun p : CompactBlockCentralizer.BlockCoefficients =>
      blockCoefficientMatrix iota W p) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let coord : EuclideanRepSpace →ₗ[ℂ] ℂ :=
    { toFun := fun x =>
        (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis.repr x i
      map_add' := by simp
      map_smul' := by simp }
  let v : EuclideanRepSpace :=
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis j
  have hVector : Continuous
      (fun p : CompactBlockCentralizer.BlockCoefficients =>
        (p.1 : ℂ) • colorComponent iota W v +
          (p.2.1 : ℂ) • weakComponent iota W v +
          (p.2.2 : ℂ) • singletComponent iota W v) := by
    fun_prop
  have hCoord : Continuous (coord : EuclideanRepSpace → ℂ) :=
    coord.continuous_of_finiteDimensional
  apply (hCoord.comp hVector).congr
  intro p
  simp only [blockCoefficientMatrix, LinearMap.toMatrix_apply]
  change coord
      ((p.1 : ℂ) • colorComponent iota W v +
        (p.2.1 : ℂ) • weakComponent iota W v +
        (p.2.2 : ℂ) • singletComponent iota W v) =
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis.repr
      (originalCircleLinearIsometryEquiv iota W p v) i
  rw [originalCircleLinearIsometryEquiv_apply,
    originalCircleLinearEquiv_apply]
  rfl

/-- Reconstruction into the actual matrix centralizer is continuous. -/
theorem continuous_reconstructedCentralizerElement
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Continuous (reconstructedCentralizerElement iota W) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun p : CompactBlockCentralizer.Group =>
    blockCoefficientMatrix iota W p.1)
  exact (continuous_blockCoefficientMatrix iota W).comp continuous_subtype_val

@[simp]
theorem reconstructedCentralizerElement_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    reconstructedCentralizerElement iota W 1 = 1 := by
  apply compactBlockCoefficientHom_injective iota W
  change compactBlockCoefficients iota W
      (reconstructedCentralizerElement iota W 1) =
    compactBlockCoefficients iota W 1
  rw [compactBlockCoefficients_reconstructed,
    compactBlockCoefficients_one]

theorem reconstructedCentralizerElement_mul
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p q : CompactBlockCentralizer.Group) :
    reconstructedCentralizerElement iota W (p * q) =
      reconstructedCentralizerElement iota W p *
        reconstructedCentralizerElement iota W q := by
  apply compactBlockCoefficientHom_injective iota W
  change compactBlockCoefficients iota W
      (reconstructedCentralizerElement iota W (p * q)) =
    compactBlockCoefficients iota W
      (reconstructedCentralizerElement iota W p *
        reconstructedCentralizerElement iota W q)
  rw [compactBlockCoefficients_reconstructed,
    compactBlockCoefficients_mul,
    compactBlockCoefficients_reconstructed,
    compactBlockCoefficients_reconstructed]

/-- Reconstruction as a group homomorphism. -/
def reconstructedCentralizerHom
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    CompactBlockCentralizer.Group →* PhysicalCentralizer iota where
  toFun := reconstructedCentralizerElement iota W
  map_one' := reconstructedCentralizerElement_one iota W
  map_mul' := reconstructedCentralizerElement_mul iota W

@[simp]
theorem reconstructedCentralizerElement_coefficients
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    reconstructedCentralizerElement iota W
        (compactBlockCoefficients iota W U) = U := by
  apply compactBlockCoefficientHom_injective iota W
  change compactBlockCoefficients iota W
      (reconstructedCentralizerElement iota W
        (compactBlockCoefficients iota W U)) =
    compactBlockCoefficients iota W U
  rw [compactBlockCoefficients_reconstructed]

/-- The explicit mutually inverse group equivalence, oriented from compact
coefficients to actual matrices. -/
def compactBlockMulEquivPhysical
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    CompactBlockCentralizer.Group ≃* PhysicalCentralizer iota where
  toFun := reconstructedCentralizerElement iota W
  invFun := compactBlockCoefficients iota W
  left_inv := compactBlockCoefficients_reconstructed iota W
  right_inv := reconstructedCentralizerElement_coefficients iota W
  map_mul' := reconstructedCentralizerElement_mul iota W

/-- The actual centralizer and the determinant-one coefficient group are
continuously group-equivalent. -/
def compactBlockContinuousMulEquivPhysical
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    CompactBlockCentralizer.Group ≃ₜ* PhysicalCentralizer iota where
  __ := compactBlockMulEquivPhysical iota W
  continuous_toFun := continuous_reconstructedCentralizerElement iota W
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (compactBlockMulEquivPhysical iota W).toEquiv)
    (continuous_reconstructedCentralizerElement iota W)

/-- The physical centralizer of the actual `3+2+1` restriction is a
topological two-torus. -/
def physicalCentralizerContinuousMulEquivTorus
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    PhysicalCentralizer iota ≃ₜ* Circle × Circle :=
  (compactBlockContinuousMulEquivPhysical iota W).symm.trans
    CompactBlockCentralizer.torusContinuousMulEquiv.symm

end

end ActualCompactCentralizer
end GUT
