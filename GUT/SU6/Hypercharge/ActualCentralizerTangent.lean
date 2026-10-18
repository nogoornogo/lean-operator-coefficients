import GUT.SU6.Hypercharge.ActualCompactCentralizerLattice
import GUT.SU6.Hypercharge.ActualSkewCentralizer
import Math.LieGroups.Torus.CircleHomTangent
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp

open Math

/-!
# Tangents of physical centralizer cocharacters

The actual matrix centralizer circle associated to `(m,n)` acts on the three
constituents by the corresponding circle power coefficients.  Differentiating
this action at the identity gives the checked anti-Hermitian
`i*(a*Y5+b*X)` element with

`a = (n-m)/5`, `b = (3m+2n)/5`.
-/

namespace GUT
namespace ActualCompactCentralizer

open WeakDoubletEmbeddingClassification
open CompactEmbeddingClassification
open ActualBlockCentralizer
open CircleHomLattice

noncomputable section

theorem centralizerIntertwiner_eq_originalCircleIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (U : PhysicalCentralizer iota) :
    centralizerIntertwiner iota U =
      originalCircleIntertwiner iota W
        (compactBlockCoefficients iota W U) := by
  calc
    centralizerIntertwiner iota U =
        centralizerIntertwiner iota
          (reconstructedCentralizerElement iota W
            (compactBlockCoefficients iota W U)) :=
      congrArg (centralizerIntertwiner iota)
        (reconstructedCentralizerElement_coefficients iota W U).symm
    _ = originalCircleIntertwiner iota W
          (compactBlockCoefficients iota W U) :=
      centralizerIntertwiner_reconstructed iota W _

/-- The action of a physical cocharacter along the standard real exponential
parameter. -/
def physicalCircleActionCurve
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (x : EuclideanRepSpace) (t : ℝ) :
    EuclideanRepSpace :=
  centralizerIntertwiner iota
    (physicalCircleHom iota W mn (Circle.exp t)) x

theorem physicalCircleActionCurve_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (x : EuclideanRepSpace) (t : ℝ) :
    physicalCircleActionCurve iota W mn x t =
      circlePowerCoefficientCurve mn.1 t • colorComponent iota W x +
        circlePowerCoefficientCurve mn.2 t • weakComponent iota W x +
        circlePowerCoefficientCurve (-(3 * mn.1 + 2 * mn.2)) t •
          singletComponent iota W x := by
  rw [physicalCircleActionCurve,
    centralizerIntertwiner_eq_originalCircleIntertwiner]
  change (originalCircleIntertwiner iota W
      (compactBlockCoefficients iota W
        (physicalCircleHom iota W mn (Circle.exp t)))).toLinearMap x = _
  rw [← originalCircleLinearEquiv_toLinearMap]
  change originalCircleLinearEquiv iota W
      (compactBlockCoefficients iota W
        (physicalCircleHom iota W mn (Circle.exp t))) x = _
  rw [originalCircleLinearEquiv_apply]
  simp only [physicalCircleHom_colorExponent,
    physicalCircleHom_weakExponent, physicalCircleHom_singletExponent]
  rfl

/-- The pointwise block action of the expected tangent generator. -/
def physicalCircleTangentVector
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (x : EuclideanRepSpace) : EuclideanRepSpace :=
  ((mn.1 : ℂ) * Complex.I) • colorComponent iota W x +
    ((mn.2 : ℂ) * Complex.I) • weakComponent iota W x +
    (((-(3 * mn.1 + 2 * mn.2) : ℤ) : ℂ) * Complex.I) •
      singletComponent iota W x

/-- The integer block tangent is exactly the checked `Y5/X` real-form
element with the associated lattice coordinates. -/
theorem physicalCircleTangentVector_eq_originalIExtra
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (x : EuclideanRepSpace) :
    physicalCircleTangentVector iota W mn x =
      ActualSkewCentralizer.originalIExtraIntertwiner iota W
        (integerPairToRealExtra mn) x := by
  let p := integerPairToRealExtra mn
  have hColor :
      -2 * (Complex.I * (p.1 : ℂ)) + Complex.I * (p.2 : ℂ) =
        (mn.1 : ℂ) * Complex.I := by
    dsimp [p, integerPairToRealExtra]
    push_cast
    ring
  have hWeak :
      3 * (Complex.I * (p.1 : ℂ)) + Complex.I * (p.2 : ℂ) =
        (mn.2 : ℂ) * Complex.I := by
    dsimp [p, integerPairToRealExtra]
    push_cast
    ring
  have hSinglet :
      -5 * (Complex.I * (p.2 : ℂ)) =
        ((-(3 * mn.1 + 2 * mn.2) : ℤ) : ℂ) * Complex.I := by
    dsimp [p, integerPairToRealExtra]
    push_cast
    ring
  rw [physicalCircleTangentVector,
    ActualSkewCentralizer.originalIExtraIntertwiner,
    ActualSkewCentralizer.originalBlockScalarIntertwiner_apply,
    hColor, hWeak, hSinglet]

/-- Differentiating the actual physical cocharacter action at the identity
gives its checked anti-Hermitian `Y5/X` generator, pointwise on the defining
representation. -/
theorem hasDerivAt_physicalCircleActionCurve
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (x : EuclideanRepSpace) :
    HasDerivAt (physicalCircleActionCurve iota W mn x)
      (ActualSkewCentralizer.originalIExtraIntertwiner iota W
        (integerPairToRealExtra mn) x) 0 := by
  rw [show physicalCircleActionCurve iota W mn x =
      (fun t : ℝ =>
        circlePowerCoefficientCurve mn.1 t • colorComponent iota W x +
          circlePowerCoefficientCurve mn.2 t • weakComponent iota W x +
          circlePowerCoefficientCurve (-(3 * mn.1 + 2 * mn.2)) t •
            singletComponent iota W x) by
    funext t
    exact physicalCircleActionCurve_apply iota W mn x t]
  have hColor : HasDerivAt
      (fun t : ℝ => circlePowerCoefficientCurve mn.1 t •
        colorComponent iota W x)
      (((mn.1 : ℂ) * Complex.I) • colorComponent iota W x) 0 :=
    (hasDerivAt_circlePowerCoefficientCurve mn.1).smul_const
      (colorComponent iota W x)
  have hWeak : HasDerivAt
      (fun t : ℝ => circlePowerCoefficientCurve mn.2 t •
        weakComponent iota W x)
      (((mn.2 : ℂ) * Complex.I) • weakComponent iota W x) 0 :=
    (hasDerivAt_circlePowerCoefficientCurve mn.2).smul_const
      (weakComponent iota W x)
  have hSinglet : HasDerivAt
      (fun t : ℝ =>
        circlePowerCoefficientCurve (-(3 * mn.1 + 2 * mn.2)) t •
          singletComponent iota W x)
      (((( -(3 * mn.1 + 2 * mn.2) : ℤ) : ℂ) * Complex.I) •
        singletComponent iota W x) 0 :=
    (hasDerivAt_circlePowerCoefficientCurve
      (-(3 * mn.1 + 2 * mn.2))).smul_const
        (singletComponent iota W x)
  rw [← physicalCircleTangentVector_eq_originalIExtra iota W mn x]
  change HasDerivAt
    (((fun t : ℝ => circlePowerCoefficientCurve mn.1 t •
          colorComponent iota W x) +
        fun t : ℝ => circlePowerCoefficientCurve mn.2 t •
          weakComponent iota W x) +
      fun t : ℝ =>
        circlePowerCoefficientCurve (-(3 * mn.1 + 2 * mn.2)) t •
          singletComponent iota W x)
      (physicalCircleTangentVector iota W mn x) 0
  exact (hColor.add hWeak).add hSinglet

/-!
## Standard-basis matrix tangent
-/

/-- The actual centralizer cocharacter written as a standard-basis matrix
curve. -/
def physicalCircleMatrixCurve
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (t : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (centralizerIntertwiner iota
      (physicalCircleHom iota W mn (Circle.exp t))).toLinearMap

/-- The checked anti-Hermitian generator written in the same standard
basis. -/
def physicalCircleTangentMatrix
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) : Matrix (Fin 6) (Fin 6) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis
    (ActualSkewCentralizer.originalIExtraIntertwiner iota W
      (integerPairToRealExtra mn)).toLinearMap

/-- The standard-basis matrix curve is the underlying matrix of the actual
physical centralizer element, not merely an auxiliary action model. -/
theorem physicalCircleMatrixCurve_eq_actual
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (t : ℝ) :
    physicalCircleMatrixCurve iota W mn t =
      (((physicalCircleHom iota W mn (Circle.exp t)).1 : SU6) :
        Matrix (Fin 6) (Fin 6) ℂ) := by
  rw [physicalCircleMatrixCurve]
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_toMatrix]
  rfl

theorem hasDerivAt_physicalCircleActionCurve_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (x : EuclideanRepSpace) (i : Fin 6) :
    HasDerivAt (fun t => physicalCircleActionCurve iota W mn x t i)
      (ActualSkewCentralizer.originalIExtraIntertwiner iota W
        (integerPairToRealExtra mn) x i) 0 := by
  simpa [Function.comp_def] using
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
      (physicalCircleActionCurve iota W mn x 0) i).comp_hasDerivAt 0
        (hasDerivAt_physicalCircleActionCurve iota W mn x))

/-- The derivative of the actual standard-basis matrix curve is exactly the
matrix of the checked anti-Hermitian `Y5/X` generator. -/
theorem hasDerivAt_physicalCircleMatrixCurve
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) :
    HasDerivAt (physicalCircleMatrixCurve iota W mn)
      (physicalCircleTangentMatrix iota W mn) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simpa [physicalCircleMatrixCurve, physicalCircleTangentMatrix,
    physicalCircleActionCurve, LinearMap.toMatrix_apply] using
    (hasDerivAt_physicalCircleActionCurve_apply iota W mn
      ((EuclideanSpace.basisFun (Fin 6) ℂ).toBasis j) i)

/-!
## Arbitrary physical cocharacters
-/

/-- The standard-basis matrix curve underlying an arbitrary continuous circle
homomorphism into the physical centralizer. -/
def physicalCocharacterMatrixCurve
    (iota : ProductGroup →* SU6)
    (f : Circle →ₜ* PhysicalCentralizer iota) (t : ℝ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  (((f (Circle.exp t)).1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)

/-- Every physical centralizer cocharacter has a unique integer exponent pair,
and differentiation of its actual `SU(6)` matrix curve gives exactly the
corresponding checked anti-Hermitian `Y5/X` generator. -/
theorem existsUnique_integerPair_and_matrix_tangent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (f : Circle →ₜ* PhysicalCentralizer iota) :
    ∃! mn : ℤ × ℤ,
      f = physicalCircleHom iota W mn ∧
        HasDerivAt (physicalCocharacterMatrixCurve iota f)
          (physicalCircleTangentMatrix iota W mn) 0 := by
  obtain ⟨mn, hmn, hmn_unique⟩ :=
    existsUnique_eq_physicalCircleHom iota W f
  refine ⟨mn, ⟨hmn, ?_⟩, ?_⟩
  · have hCurve : physicalCocharacterMatrixCurve iota f =
        physicalCircleMatrixCurve iota W mn := by
      funext t
      rw [physicalCocharacterMatrixCurve, hmn,
        physicalCircleMatrixCurve_eq_actual]
    rw [hCurve]
    exact hasDerivAt_physicalCircleMatrixCurve iota W mn
  · intro pq hpq
    exact hmn_unique pq hpq.1

end

end ActualCompactCentralizer
end GUT
