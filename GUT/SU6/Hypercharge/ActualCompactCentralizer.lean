import GUT.SU6.Hypercharge.CompactBlockCentralizer
import Math.RepresentationTheory.Unitary.UnitarySubrepresentationOrthogonality
import Mathlib.GroupTheory.Subgroup.Centralizer

open Math

/-!
# The compact centralizer of an actual `SU(3) x SU(2)` embedding

This file connects the abstract compact block-coefficient group to the
centralizer of the image of an actual homomorphism into `SU(6)`.
-/

namespace GUT
namespace ActualCompactCentralizer

open WeakDoubletEmbeddingClassification
open CompactEmbeddingClassification
open ActualBlockCentralizer
open UnitarySubrepresentationOrthogonality

noncomputable section

/-- The centralizer in `SU(6)` of the image of a proposed semisimple
embedding. -/
abbrev PhysicalCentralizer (iota : ProductGroup →* SU6) : Subgroup SU6 :=
  Subgroup.centralizer (Set.range iota)

/-- A centralizing special-unitary matrix acts as an intertwiner of the
restricted Euclidean defining representation. -/
def centralizerIntertwiner (iota : ProductGroup →* SU6)
    (U : PhysicalCentralizer iota) :
    Representation.IntertwiningMap
      (euclideanDefiningRestriction iota)
      (euclideanDefiningRestriction iota) where
  toLinearMap := Matrix.toEuclideanLin
    (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change
      Matrix.toEuclideanLin (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
          (Matrix.toEuclideanLin
            (((iota g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) x) =
        Matrix.toEuclideanLin
            (((iota g : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
          (Matrix.toEuclideanLin
            (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) x)
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same]
    exact congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ =>
        Matrix.toEuclideanLin M x)
      (congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp U.2 (iota g)
          ⟨g, rfl⟩).symm))

@[simp]
theorem centralizerIntertwiner_apply (iota : ProductGroup →* SU6)
    (U : PhysicalCentralizer iota) (x : EuclideanRepSpace) :
    centralizerIntertwiner iota U x =
      Matrix.toEuclideanLin
        (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) x :=
  rfl

@[simp]
theorem centralizerIntertwiner_one (iota : ProductGroup →* SU6) :
    centralizerIntertwiner iota 1 = 1 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp [centralizerIntertwiner, Matrix.toLpLin_one]

theorem centralizerIntertwiner_mul (iota : ProductGroup →* SU6)
    (U V : PhysicalCentralizer iota) :
    centralizerIntertwiner iota (U * V) =
      (centralizerIntertwiner iota U).comp
        (centralizerIntertwiner iota V) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change
    Matrix.toEuclideanLin
        (((((U * V).1 : SU6)) : Matrix (Fin 6) (Fin 6) ℂ)) x =
      Matrix.toEuclideanLin
          (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
        (Matrix.toEuclideanLin
          (((V.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) x)
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
  rfl

/-- The actual centralizer action transported to the three ordered semisimple embedding classification
constituents. -/
def transportedCentralizerIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    Representation.IntertwiningMap
      (orderedBlockRepresentation W) (orderedBlockRepresentation W) :=
  BlockCentralizer.transportCommutant
    (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
    (representationEquivOrderedBlocks W) (centralizerIntertwiner iota U)

@[simp]
theorem transportedCentralizerIntertwiner_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    transportedCentralizerIntertwiner iota W 1 = 1 := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp [transportedCentralizerIntertwiner,
    BlockCentralizer.transportCommutant_apply]

theorem transportedCentralizerIntertwiner_mul
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U V : PhysicalCentralizer iota) :
    transportedCentralizerIntertwiner iota W (U * V) =
      (transportedCentralizerIntertwiner iota W U).comp
        (transportedCentralizerIntertwiner iota W V) := by
  rw [transportedCentralizerIntertwiner,
    centralizerIntertwiner_mul]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp [transportedCentralizerIntertwiner,
    BlockCentralizer.transportCommutant_apply]

/-- Scalar block intertwiners multiply coefficientwise. -/
theorem orderedBlockScalarIntertwiner_comp
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (c w s c' w' s' : ℂ) :
    (orderedBlockScalarIntertwiner W c w s).comp
        (orderedBlockScalarIntertwiner W c' w' s') =
      orderedBlockScalarIntertwiner W (c * c') (w * w') (s * s') := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  rintro ⟨xColor, xWeak, xSinglet⟩
  simp [orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap,
    smul_smul, mul_comm]

/-- The three complex block coefficients of a centralizer element exist and
are unique. -/
theorem existsUnique_complexBlockCoefficients
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ∃! p : ℂ × (ℂ × ℂ),
      transportedCentralizerIntertwiner iota W U =
        orderedBlockScalarIntertwiner W p.1 p.2.1 p.2.2 := by
  obtain ⟨c, w, s, h⟩ :=
    orderedBlock_commutant_eq_blockScalarIntertwiner W
      (transportedCentralizerIntertwiner iota W U)
  refine ⟨(c, (w, s)), h, ?_⟩
  rintro ⟨c', w', s'⟩ h'
  have hCoefficients :=
    (orderedBlockScalarIntertwiner_eq_iff W).mp (h.symm.trans h')
  exact Prod.ext hCoefficients.1.symm
    (Prod.ext hCoefficients.2.1.symm hCoefficients.2.2.symm)

/-- The canonically selected complex block coefficients.  Their uniqueness,
not the implementation of `Classical.choose`, controls all later proofs. -/
def complexBlockCoefficients
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) : ℂ × (ℂ × ℂ) :=
  Classical.choose (existsUnique_complexBlockCoefficients iota W U)

theorem complexBlockCoefficients_spec
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    transportedCentralizerIntertwiner iota W U =
      orderedBlockScalarIntertwiner W
        (complexBlockCoefficients iota W U).1
        (complexBlockCoefficients iota W U).2.1
        (complexBlockCoefficients iota W U).2.2 :=
  (Classical.choose_spec
    (existsUnique_complexBlockCoefficients iota W U)).1

theorem complexBlockCoefficients_eq_of_spec
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) (p : ℂ × (ℂ × ℂ))
    (hp : transportedCentralizerIntertwiner iota W U =
      orderedBlockScalarIntertwiner W p.1 p.2.1 p.2.2) :
    complexBlockCoefficients iota W U = p := by
  exact ((Classical.choose_spec
    (existsUnique_complexBlockCoefficients iota W U)).2 p hp).symm

@[simp]
theorem complexBlockCoefficients_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    complexBlockCoefficients iota W 1 = 1 := by
  apply complexBlockCoefficients_eq_of_spec
  rw [transportedCentralizerIntertwiner_one]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  rintro ⟨xColor, xWeak, xSinglet⟩
  simp [orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap]

theorem complexBlockCoefficients_mul
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U V : PhysicalCentralizer iota) :
    complexBlockCoefficients iota W (U * V) =
      complexBlockCoefficients iota W U *
        complexBlockCoefficients iota W V := by
  apply complexBlockCoefficients_eq_of_spec
  rw [transportedCentralizerIntertwiner_mul,
    complexBlockCoefficients_spec iota W U,
    complexBlockCoefficients_spec iota W V]
  exact orderedBlockScalarIntertwiner_comp iota W _ _ _ _ _ _

/-- Complex block coefficients form a monoid homomorphism before unitarity
is used to restrict their values to the circle. -/
def complexBlockCoefficientHom
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    PhysicalCentralizer iota →* ℂ × (ℂ × ℂ) where
  toFun := complexBlockCoefficients iota W
  map_one' := complexBlockCoefficients_one iota W
  map_mul' := complexBlockCoefficients_mul iota W

/-- The action of a centralizer element preserves the Euclidean norm. -/
theorem centralizerIntertwiner_norm_map
    (iota : ProductGroup →* SU6) (U : PhysicalCentralizer iota)
    (x : EuclideanRepSpace) :
    ‖centralizerIntertwiner iota U x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),
    norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  congr 1
  apply congrArg Complex.re
  apply unitaryMatrix_preserves_inner
  have hUnitary :
      (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ) :
          Matrix (Fin 6) (Fin 6) ℂ) ∈ Matrix.unitaryGroup (Fin 6) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup U.1.prop
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hUnitary)

/-- A norm-preserving linear map can only have a unit-modulus eigenvalue on
a nonzero eigenvector. -/
theorem norm_eigenvalue_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E →ₗ[ℂ] E) (c : ℂ) (x : E) (hx : x ≠ 0)
    (hf : f x = c • x) (hNorm : ‖f x‖ = ‖x‖) :
    ‖c‖ = 1 := by
  rw [hf, norm_smul] at hNorm
  apply mul_right_cancel₀ (norm_ne_zero_iff.mpr hx)
  simpa using hNorm

theorem colorCoefficient_norm_eq_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ‖(complexBlockCoefficients iota W U).1‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : ColorBlockSpace W)
  let y : OrderedBlockSpace W := (x, (0, 0))
  let e := representationEquivOrderedBlocks W
  have hy : y ≠ 0 := by
    intro h
    exact hx (congrArg Prod.fst h)
  have hex : e.symm y ≠ 0 := by
    intro h
    apply hy
    simpa [e] using congrArg e h
  have hEigen :
      centralizerIntertwiner iota U (e.symm y) =
        (complexBlockCoefficients iota W U).1 • e.symm y := by
    apply e.injective
    have hApply := congrArg
      (fun f : Representation.IntertwiningMap
          (orderedBlockRepresentation W) (orderedBlockRepresentation W) =>
        f y)
      (complexBlockCoefficients_spec iota W U)
    simpa [transportedCentralizerIntertwiner,
      BlockCentralizer.transportCommutant_apply,
      orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap, y, e]
      using hApply
  exact norm_eigenvalue_eq_one
    (centralizerIntertwiner iota U).toLinearMap
    (complexBlockCoefficients iota W U).1 (e.symm y) hex hEigen
    (centralizerIntertwiner_norm_map iota U (e.symm y))

theorem weakCoefficient_norm_eq_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ‖(complexBlockCoefficients iota W U).2.1‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : WeakBlockSpace W)
  let y : OrderedBlockSpace W := (0, (x, 0))
  let e := representationEquivOrderedBlocks W
  have hy : y ≠ 0 := by
    intro h
    exact hx (congrArg (fun q => q.2.1) h)
  have hex : e.symm y ≠ 0 := by
    intro h
    apply hy
    simpa [e] using congrArg e h
  have hEigen :
      centralizerIntertwiner iota U (e.symm y) =
        (complexBlockCoefficients iota W U).2.1 • e.symm y := by
    apply e.injective
    have hApply := congrArg
      (fun f : Representation.IntertwiningMap
          (orderedBlockRepresentation W) (orderedBlockRepresentation W) =>
        f y)
      (complexBlockCoefficients_spec iota W U)
    simpa [transportedCentralizerIntertwiner,
      BlockCentralizer.transportCommutant_apply,
      orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap, y, e]
      using hApply
  exact norm_eigenvalue_eq_one
    (centralizerIntertwiner iota U).toLinearMap
    (complexBlockCoefficients iota W U).2.1 (e.symm y) hex hEigen
    (centralizerIntertwiner_norm_map iota U (e.symm y))

theorem singletCoefficient_norm_eq_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ‖(complexBlockCoefficients iota W U).2.2‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : SingletBlockSpace W)
  let y : OrderedBlockSpace W := (0, (0, x))
  let e := representationEquivOrderedBlocks W
  have hy : y ≠ 0 := by
    intro h
    exact hx (congrArg (fun q => q.2.2) h)
  have hex : e.symm y ≠ 0 := by
    intro h
    apply hy
    simpa [e] using congrArg e h
  have hEigen :
      centralizerIntertwiner iota U (e.symm y) =
        (complexBlockCoefficients iota W U).2.2 • e.symm y := by
    apply e.injective
    have hApply := congrArg
      (fun f : Representation.IntertwiningMap
          (orderedBlockRepresentation W) (orderedBlockRepresentation W) =>
        f y)
      (complexBlockCoefficients_spec iota W U)
    simpa [transportedCentralizerIntertwiner,
      BlockCentralizer.transportCommutant_apply,
      orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap, y, e]
      using hApply
  exact norm_eigenvalue_eq_one
    (centralizerIntertwiner iota U).toLinearMap
    (complexBlockCoefficients iota W U).2.2 (e.symm y) hex hEigen
    (centralizerIntertwiner_norm_map iota U (e.symm y))

/-- The determinant of the Euclidean linear action is the matrix determinant,
and hence is one for a centralizer element in `SU(6)`. -/
theorem centralizerIntertwiner_det_one
    (iota : ProductGroup →* SU6) (U : PhysicalCentralizer iota) :
    LinearMap.det (centralizerIntertwiner iota U).toLinearMap = 1 := by
  have hMatrixDet :
      Matrix.det (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) = 1 :=
    (U.1 : SU6).prop.2
  change LinearMap.det
    (Matrix.toEuclideanLin
      (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ))) = 1
  rw [LinearMap.det_toLpLin]
  exact hMatrixDet

/-- The actual complex block coefficients obey the special-unitary
determinant equation. -/
theorem complexBlockCoefficients_det_eq_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    (complexBlockCoefficients iota W U).1 ^ 3 *
          (complexBlockCoefficients iota W U).2.1 ^ 2 *
          (complexBlockCoefficients iota W U).2.2 = 1 := by
  have hDet :
      LinearMap.det
          (transportedCentralizerIntertwiner iota W U).toLinearMap = 1 := by
    rw [transportedCentralizerIntertwiner,
      BlockCentralizer.det_transportCommutant]
    exact centralizerIntertwiner_det_one iota U
  rw [complexBlockCoefficients_spec iota W U] at hDet
  simpa [orderedBlockScalarIntertwiner,
    det_orderedBlockScalarLinearMap] using hDet

/-- The unit-circle-valued block coefficients. -/
def circleBlockCoefficients
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
  CompactBlockCentralizer.BlockCoefficients :=
  (⟨(complexBlockCoefficients iota W U).1,
      by simpa [Submonoid.unitSphere] using
        colorCoefficient_norm_eq_one iota W U⟩,
    (⟨(complexBlockCoefficients iota W U).2.1,
        by simpa [Submonoid.unitSphere] using
          weakCoefficient_norm_eq_one iota W U⟩,
      ⟨(complexBlockCoefficients iota W U).2.2,
        by simpa [Submonoid.unitSphere] using
          singletCoefficient_norm_eq_one iota W U⟩))

@[simp]
theorem circleBlockCoefficients_color_coe
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ((circleBlockCoefficients iota W U).1 : ℂ) =
      (complexBlockCoefficients iota W U).1 :=
  rfl

@[simp]
theorem circleBlockCoefficients_weak_coe
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ((circleBlockCoefficients iota W U).2.1 : ℂ) =
      (complexBlockCoefficients iota W U).2.1 :=
  rfl

@[simp]
theorem circleBlockCoefficients_singlet_coe
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    ((circleBlockCoefficients iota W U).2.2 : ℂ) =
      (complexBlockCoefficients iota W U).2.2 :=
  rfl

/-- Every actual centralizer element maps into the determinant-one compact
coefficient group. -/
def compactBlockCoefficients
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) : CompactBlockCentralizer.Group :=
  ⟨circleBlockCoefficients iota W U, by
    change
      (circleBlockCoefficients iota W U).1 ^ 3 *
          (circleBlockCoefficients iota W U).2.1 ^ 2 *
          (circleBlockCoefficients iota W U).2.2 = 1
    apply Circle.ext
    simpa using complexBlockCoefficients_det_eq_one iota W U⟩

@[simp]
theorem compactBlockCoefficients_one
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    compactBlockCoefficients iota W 1 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · apply Circle.ext
    simp [compactBlockCoefficients, circleBlockCoefficients]
  · apply Prod.ext <;> apply Circle.ext <;>
      simp [compactBlockCoefficients, circleBlockCoefficients]

theorem compactBlockCoefficients_mul
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U V : PhysicalCentralizer iota) :
    compactBlockCoefficients iota W (U * V) =
      compactBlockCoefficients iota W U *
        compactBlockCoefficients iota W V := by
  apply Subtype.ext
  apply Prod.ext
  · apply Circle.ext
    exact congrArg Prod.fst (complexBlockCoefficients_mul iota W U V)
  · apply Prod.ext
    · apply Circle.ext
      exact congrArg (fun p : ℂ × (ℂ × ℂ) => p.2.1)
        (complexBlockCoefficients_mul iota W U V)
    · apply Circle.ext
      exact congrArg (fun p : ℂ × (ℂ × ℂ) => p.2.2)
        (complexBlockCoefficients_mul iota W U V)

/-- The actual `SU(6)` centralizer embeds homomorphically into the abstract
rank-two compact coefficient group. -/
def compactBlockCoefficientHom
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    PhysicalCentralizer iota →* CompactBlockCentralizer.Group where
  toFun := compactBlockCoefficients iota W
  map_one' := compactBlockCoefficients_one iota W
  map_mul' := compactBlockCoefficients_mul iota W

theorem centralizerIntertwiner_injective (iota : ProductGroup →* SU6) :
    Function.Injective (centralizerIntertwiner iota) := by
  intro U V h
  have hLinear := congrArg Representation.IntertwiningMap.toLinearMap h
  have hMatrix :
      (((U.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) =
        (((V.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) :=
    Matrix.toEuclideanLin.injective hLinear
  apply Subtype.ext
  apply Subtype.ext
  exact hMatrix

/-- No information is lost when a physical centralizer element is replaced
by its three unitary block coefficients. -/
theorem compactBlockCoefficientHom_injective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Injective (compactBlockCoefficientHom iota W) := by
  intro U V h
  have hComplex :
      complexBlockCoefficients iota W U =
        complexBlockCoefficients iota W V := by
    apply Prod.ext
    · simpa [compactBlockCoefficientHom, compactBlockCoefficients,
        circleBlockCoefficients] using congrArg
          (fun p : CompactBlockCentralizer.Group =>
            ((p.1.1 : Circle) : ℂ)) h
    · apply Prod.ext
      · simpa [compactBlockCoefficientHom, compactBlockCoefficients,
          circleBlockCoefficients] using congrArg
          (fun p : CompactBlockCentralizer.Group =>
            ((p.1.2.1 : Circle) : ℂ)) h
      · simpa [compactBlockCoefficientHom, compactBlockCoefficients,
          circleBlockCoefficients] using congrArg
          (fun p : CompactBlockCentralizer.Group =>
            ((p.1.2.2 : Circle) : ℂ)) h
  apply centralizerIntertwiner_injective iota
  apply BlockCentralizer.transportCommutant_injective
    (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
    (representationEquivOrderedBlocks W)
  change transportedCentralizerIntertwiner iota W U =
    transportedCentralizerIntertwiner iota W V
  rw [complexBlockCoefficients_spec iota W U,
    complexBlockCoefficients_spec iota W V, hComplex]

/-!
## Orthogonal coordinate constituents
-/

/-- The color coordinate of the ordered decomposition, embedded back into
the original Euclidean representation. -/
def colorCoordinateIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Representation.IntertwiningMap (colorBlockRepresentation W)
      (euclideanDefiningRestriction iota) :=
  (representationEquivOrderedBlocks W).symm.toIntertwiningMap.comp
    (Representation.IntertwiningMap.inl ℂ (colorBlockRepresentation W)
      ((weakBlockRepresentation W).prod (singletBlockRepresentation W)))

/-- The weak coordinate embedded back into the original representation. -/
def weakCoordinateIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Representation.IntertwiningMap (weakBlockRepresentation W)
      (euclideanDefiningRestriction iota) :=
  (representationEquivOrderedBlocks W).symm.toIntertwiningMap.comp
    ((Representation.IntertwiningMap.inr ℂ (colorBlockRepresentation W)
      ((weakBlockRepresentation W).prod (singletBlockRepresentation W))).comp
      (Representation.IntertwiningMap.inl ℂ (weakBlockRepresentation W)
        (singletBlockRepresentation W)))

/-- The singlet coordinate embedded back into the original representation. -/
def singletCoordinateIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Representation.IntertwiningMap (singletBlockRepresentation W)
      (euclideanDefiningRestriction iota) :=
  (representationEquivOrderedBlocks W).symm.toIntertwiningMap.comp
    ((Representation.IntertwiningMap.inr ℂ (colorBlockRepresentation W)
      ((weakBlockRepresentation W).prod (singletBlockRepresentation W))).comp
      (Representation.IntertwiningMap.inr ℂ (weakBlockRepresentation W)
        (singletBlockRepresentation W)))

@[simp]
theorem colorCoordinateIntertwiner_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : ColorBlockSpace W) :
    colorCoordinateIntertwiner iota W x =
      (representationEquivOrderedBlocks W).symm (x, (0, 0)) :=
  rfl

@[simp]
theorem weakCoordinateIntertwiner_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : WeakBlockSpace W) :
    weakCoordinateIntertwiner iota W x =
      (representationEquivOrderedBlocks W).symm (0, (x, 0)) :=
  rfl

@[simp]
theorem singletCoordinateIntertwiner_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (x : SingletBlockSpace W) :
    singletCoordinateIntertwiner iota W x =
      (representationEquivOrderedBlocks W).symm (0, (0, x)) :=
  rfl

theorem colorCoordinateIntertwiner_injective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Injective (colorCoordinateIntertwiner iota W) := by
  intro x y h
  have h' := congrArg (representationEquivOrderedBlocks W) h
  simpa using congrArg Prod.fst h'

theorem weakCoordinateIntertwiner_injective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Injective (weakCoordinateIntertwiner iota W) := by
  intro x y h
  have h' := congrArg (representationEquivOrderedBlocks W) h
  simpa using congrArg (fun p => p.2.1) h'

theorem singletCoordinateIntertwiner_injective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Injective (singletCoordinateIntertwiner iota W) := by
  intro x y h
  have h' := congrArg (representationEquivOrderedBlocks W) h
  simpa using congrArg (fun p => p.2.2) h'

/-- The color and weak coordinate ranges selected by the decomposition
equivalence are orthogonal in the original Euclidean space. -/
theorem colorRange_isOrtho_weakRange
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    (colorCoordinateIntertwiner iota W).range.toSubmodule ⟂
      (weakCoordinateIntertwiner iota W).range.toSubmodule := by
  let : Representation.IsIrreducible
      (colorCoordinateIntertwiner iota W).range.toRepresentation :=
    range_isIrreducible _ (colorCoordinateIntertwiner_injective iota W)
  let : Representation.IsIrreducible
      (weakCoordinateIntertwiner iota W).range.toRepresentation :=
    range_isIrreducible _ (weakCoordinateIntertwiner_injective iota W)
  apply isOrtho_of_irreducible_of_finrank_ne
    (euclideanDefiningRestriction iota)
    (euclideanDefiningRestriction_unitary iota)
  rw [finrank_range_eq _ (colorCoordinateIntertwiner_injective iota W),
    finrank_range_eq _ (weakCoordinateIntertwiner_injective iota W)]
  simp [ColorBlockSpace, WeakBlockSpace]

/-- The color and singlet coordinate ranges are orthogonal. -/
theorem colorRange_isOrtho_singletRange
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    (colorCoordinateIntertwiner iota W).range.toSubmodule ⟂
      (singletCoordinateIntertwiner iota W).range.toSubmodule := by
  let : Representation.IsIrreducible
      (colorCoordinateIntertwiner iota W).range.toRepresentation :=
    range_isIrreducible _ (colorCoordinateIntertwiner_injective iota W)
  let : Representation.IsIrreducible
      (singletCoordinateIntertwiner iota W).range.toRepresentation :=
    range_isIrreducible _ (singletCoordinateIntertwiner_injective iota W)
  apply isOrtho_of_irreducible_of_finrank_ne
    (euclideanDefiningRestriction iota)
    (euclideanDefiningRestriction_unitary iota)
  rw [finrank_range_eq _ (colorCoordinateIntertwiner_injective iota W),
    finrank_range_eq _ (singletCoordinateIntertwiner_injective iota W)]
  simp [ColorBlockSpace, SingletBlockSpace]

/-- The weak and singlet coordinate ranges are orthogonal. -/
theorem weakRange_isOrtho_singletRange
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    (weakCoordinateIntertwiner iota W).range.toSubmodule ⟂
      (singletCoordinateIntertwiner iota W).range.toSubmodule := by
  let : Representation.IsIrreducible
      (weakCoordinateIntertwiner iota W).range.toRepresentation :=
    range_isIrreducible _ (weakCoordinateIntertwiner_injective iota W)
  let : Representation.IsIrreducible
      (singletCoordinateIntertwiner iota W).range.toRepresentation :=
    range_isIrreducible _ (singletCoordinateIntertwiner_injective iota W)
  apply isOrtho_of_irreducible_of_finrank_ne
    (euclideanDefiningRestriction iota)
    (euclideanDefiningRestriction_unitary iota)
  rw [finrank_range_eq _ (weakCoordinateIntertwiner_injective iota W),
    finrank_range_eq _ (singletCoordinateIntertwiner_injective iota W)]
  simp [WeakBlockSpace, SingletBlockSpace]

end


end ActualCompactCentralizer
end GUT
