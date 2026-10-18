import GUT.SU6.Hypercharge.ActualCompactCentralizerEquivalence
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Complex.Module

/-!
# The anti-Hermitian real form of the actual centralizer

The complexified commutant has two complex `Y5/X` coefficients.  This file
intersects it with the skew-adjoint, trace-zero endomorphisms of the original
Euclidean representation and proves that the coefficients are exactly
`i * a` and `i * b` for unique real numbers `a` and `b`.
-/

namespace GUT
namespace ActualSkewCentralizer

open WeakDoubletEmbeddingClassification
open CompactEmbeddingClassification
open ActualBlockCentralizer
open ActualCompactCentralizer

noncomputable section

/-- A nonzero eigenvector of a skew-adjoint operator has a purely imaginary
eigenvalue. -/
theorem eigenvalue_star_eq_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] E) (c : ℂ) (x : E) (hx : x ≠ 0)
    (hEigen : f x = c • x)
    (hSkew : f ∈ skewAdjoint (E →ₗ[ℂ] E)) :
    starRingEnd ℂ c = -c := by
  have hStar := skewAdjoint.mem_iff.mp hSkew
  rw [LinearMap.star_eq_adjoint] at hStar
  have hInner := LinearMap.adjoint_inner_right f x x
  rw [hStar, LinearMap.neg_apply, hEigen] at hInner
  rw [← neg_smul, inner_smul_right, inner_smul_left] at hInner
  have hCoeff := mul_right_cancel₀ (inner_self_ne_zero.mpr hx) hInner
  exact hCoeff.symm

/-- The color block coefficient of a skew-adjoint actual commutant element is
purely imaginary. -/
theorem colorCoefficient_star_eq_neg
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (f : Representation.IntertwiningMap
      (euclideanDefiningRestriction iota) (euclideanDefiningRestriction iota))
    (c w s : ℂ)
    (hSpec : BlockCentralizer.transportCommutant
        (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
        (representationEquivOrderedBlocks W) f =
      orderedBlockScalarIntertwiner W c w s)
    (hSkew : f.toLinearMap ∈
      skewAdjoint (EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace)) :
    starRingEnd ℂ c = -c := by
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
  have hEigen : f (e.symm y) = c • e.symm y := by
    apply e.injective
    have hApply := congrArg
      (fun q : Representation.IntertwiningMap
          (orderedBlockRepresentation W) (orderedBlockRepresentation W) => q y)
      hSpec
    simpa [BlockCentralizer.transportCommutant_apply,
      orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap, y, e]
      using hApply
  exact eigenvalue_star_eq_neg f.toLinearMap c (e.symm y) hex hEigen hSkew

/-- The weak block coefficient of a skew-adjoint actual commutant element is
purely imaginary. -/
theorem weakCoefficient_star_eq_neg
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (f : Representation.IntertwiningMap
      (euclideanDefiningRestriction iota) (euclideanDefiningRestriction iota))
    (c w s : ℂ)
    (hSpec : BlockCentralizer.transportCommutant
        (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
        (representationEquivOrderedBlocks W) f =
      orderedBlockScalarIntertwiner W c w s)
    (hSkew : f.toLinearMap ∈
      skewAdjoint (EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace)) :
    starRingEnd ℂ w = -w := by
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
  have hEigen : f (e.symm y) = w • e.symm y := by
    apply e.injective
    have hApply := congrArg
      (fun q : Representation.IntertwiningMap
          (orderedBlockRepresentation W) (orderedBlockRepresentation W) => q y)
      hSpec
    simpa [BlockCentralizer.transportCommutant_apply,
      orderedBlockScalarIntertwiner, orderedBlockScalarLinearMap, y, e]
      using hApply
  exact eigenvalue_star_eq_neg f.toLinearMap w (e.symm y) hex hEigen hSkew

theorem re_eq_zero_of_star_eq_neg (z : ℂ)
    (h : starRingEnd ℂ z = -z) : z.re = 0 := by
  have hRe := congrArg Complex.re h
  simp at hRe
  linarith

theorem eq_I_mul_im_of_re_eq_zero (z : ℂ) (h : z.re = 0) :
    z = Complex.I * (z.im : ℂ) := by
  apply Complex.ext
  · simp [h]
  · simp

/-- Every skew-adjoint traceless actual commutant element has unique real
coefficients in the anti-Hermitian directions `i*Y5` and `i*X`. -/
theorem skew_traceless_commutant_eq_iOrderedExtra_unique
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (f : Representation.IntertwiningMap
      (euclideanDefiningRestriction iota) (euclideanDefiningRestriction iota))
    (hSkew : f.toLinearMap ∈
      skewAdjoint (EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace))
    (hTrace : LinearMap.trace ℂ EuclideanRepSpace f.toLinearMap = 0) :
    ∃! p : ℝ × ℝ,
      BlockCentralizer.transportCommutant
          (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
          (representationEquivOrderedBlocks W) f =
        orderedExtraIntertwiner W
          (Complex.I * (p.1 : ℂ)) (Complex.I * (p.2 : ℂ)) := by
  obtain ⟨⟨a, b⟩, hExtra, hUnique⟩ :=
    traceless_actual_commutant_eq_orderedExtra_unique W f hTrace
  have hSpec : BlockCentralizer.transportCommutant
        (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
        (representationEquivOrderedBlocks W) f =
      orderedBlockScalarIntertwiner W (-2 * a + b) (3 * a + b) (-5 * b) := by
    simpa [orderedExtraIntertwiner] using hExtra
  have hcStar := colorCoefficient_star_eq_neg iota W f
    (-2 * a + b) (3 * a + b) (-5 * b) hSpec hSkew
  have hwStar := weakCoefficient_star_eq_neg iota W f
    (-2 * a + b) (3 * a + b) (-5 * b) hSpec hSkew
  have hcRe := re_eq_zero_of_star_eq_neg (-2 * a + b) hcStar
  have hwRe := re_eq_zero_of_star_eq_neg (3 * a + b) hwStar
  have haRe : a.re = 0 := by
    norm_num at hcRe hwRe
    linarith
  have hbRe : b.re = 0 := by
    norm_num at hcRe hwRe
    linarith
  have haI := eq_I_mul_im_of_re_eq_zero a haRe
  have hbI := eq_I_mul_im_of_re_eq_zero b hbRe
  refine ⟨(a.im, b.im), ?_, ?_⟩
  · change BlockCentralizer.transportCommutant
        (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
        (representationEquivOrderedBlocks W) f =
      orderedExtraIntertwiner W
        (Complex.I * (a.im : ℂ)) (Complex.I * (b.im : ℂ))
    rw [← haI, ← hbI]
    exact hExtra
  · rintro ⟨a', b'⟩ h'
    have hComplex :
        (Complex.I * (a' : ℂ), Complex.I * (b' : ℂ)) = (a, b) :=
      hUnique _ h'
    apply Prod.ext
    · have hIm := congrArg (fun q : ℂ × ℂ => q.1.im) hComplex
      simpa using hIm
    · have hIm := congrArg (fun q : ℂ × ℂ => q.2.im) hComplex
      simpa using hIm

/-!
## The converse construction
-/

/-- Scalar action on the actual blocks, conjugated back to the original
representation. -/
def originalBlockScalarIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (c w s : ℂ) :
    Representation.IntertwiningMap
      (euclideanDefiningRestriction iota) (euclideanDefiningRestriction iota) :=
  (representationEquivOrderedBlocks W).symm.toIntertwiningMap.comp
    ((orderedBlockScalarIntertwiner W c w s).comp
      (representationEquivOrderedBlocks W).toIntertwiningMap)

@[simp]
theorem originalBlockScalarIntertwiner_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (c w s : ℂ) (x : EuclideanRepSpace) :
    originalBlockScalarIntertwiner iota W c w s x =
      c • colorComponent iota W x + w • weakComponent iota W x +
        s • singletComponent iota W x := by
  apply (representationEquivOrderedBlocks W).injective
  simp [originalBlockScalarIntertwiner, orderedBlockScalarIntertwiner,
    orderedBlockScalarLinearMap, colorComponent, weakComponent, singletComponent]

theorem trace_originalBlockScalarIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (c w s : ℂ) :
    LinearMap.trace ℂ EuclideanRepSpace
        (originalBlockScalarIntertwiner iota W c w s).toLinearMap =
      3 * c + 2 * w + s := by
  rw [originalBlockScalarIntertwiner]
  simp only [Representation.IntertwiningMap.comp_toLinearMap]
  have hConj := LinearMap.trace_conj'
    (orderedBlockScalarIntertwiner W c w s).toLinearMap
    (representationEquivOrderedBlocks W).toLinearEquiv.symm
  calc
    _ = LinearMap.trace ℂ (OrderedBlockSpace W)
        (orderedBlockScalarIntertwiner W c w s).toLinearMap := by
      convert hConj using 1
      simp only [Representation.Equiv.toLinearMap_symm]
      congr 1
    _ = _ := trace_orderedBlockScalarLinearMap W c w s

/-- Purely imaginary block coefficients give an infinitesimally unitary
operator on the original Euclidean space. -/
theorem originalBlockScalarIntertwiner_inner_skew
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (c w s : ℂ)
    (hc : starRingEnd ℂ c = -c) (hw : starRingEnd ℂ w = -w)
    (hs : starRingEnd ℂ s = -s) (x y : EuclideanRepSpace) :
    inner ℂ (originalBlockScalarIntertwiner iota W c w s x) y =
      -inner ℂ x (originalBlockScalarIntertwiner iota W c w s y) := by
  rw [originalBlockScalarIntertwiner_apply,
    originalBlockScalarIntertwiner_apply]
  calc
    _ = inner ℂ
        (c • colorComponent iota W x + w • weakComponent iota W x +
          s • singletComponent iota W x)
        (colorComponent iota W y + weakComponent iota W y +
          singletComponent iota W y) := by rw [component_sum]
    _ = -inner ℂ
        (colorComponent iota W x + weakComponent iota W x +
          singletComponent iota W x)
        (c • colorComponent iota W y + w • weakComponent iota W y +
          s • singletComponent iota W y) := by
      simp only [inner_add_left, inner_add_right]
      simp [inner_smul_left, inner_smul_right, hc, hw, hs,
        colorComponent_inner_weakComponent,
        colorComponent_inner_singletComponent,
        weakComponent_inner_singletComponent,
        inner_eq_zero_symm.mpr
          (colorComponent_inner_weakComponent iota W y x),
        inner_eq_zero_symm.mpr
          (colorComponent_inner_singletComponent iota W y x),
        inner_eq_zero_symm.mpr
          (weakComponent_inner_singletComponent iota W y x)]
      ring
    _ = -inner ℂ x
        (c • colorComponent iota W y + w • weakComponent iota W y +
          s • singletComponent iota W y) := by rw [component_sum]

theorem originalBlockScalarIntertwiner_mem_skewAdjoint
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (c w s : ℂ)
    (hc : starRingEnd ℂ c = -c) (hw : starRingEnd ℂ w = -w)
    (hs : starRingEnd ℂ s = -s) :
    (originalBlockScalarIntertwiner iota W c w s).toLinearMap ∈
      skewAdjoint (EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace) := by
  rw [skewAdjoint.mem_iff, LinearMap.star_eq_adjoint]
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (originalBlockScalarIntertwiner iota W c w s x) y =
    inner ℂ x (-originalBlockScalarIntertwiner iota W c w s y)
  rw [inner_neg_right]
  exact originalBlockScalarIntertwiner_inner_skew
    iota W c w s hc hw hs x y

theorem star_eq_neg_of_re_eq_zero (z : ℂ) (h : z.re = 0) :
    starRingEnd ℂ z = -z := by
  apply Complex.ext
  · simp [h]
  · simp

/-- The original-space realization of `i * (a*Y5 + b*X)`. -/
def originalIExtraIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : ℝ × ℝ) :
    Representation.IntertwiningMap
      (euclideanDefiningRestriction iota) (euclideanDefiningRestriction iota) :=
  originalBlockScalarIntertwiner iota W
    (-2 * (Complex.I * (p.1 : ℂ)) + Complex.I * (p.2 : ℂ))
    (3 * (Complex.I * (p.1 : ℂ)) + Complex.I * (p.2 : ℂ))
    (-5 * (Complex.I * (p.2 : ℂ)))

theorem originalIExtraIntertwiner_trace_zero
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : ℝ × ℝ) :
    LinearMap.trace ℂ EuclideanRepSpace
      (originalIExtraIntertwiner iota W p).toLinearMap = 0 := by
  rw [originalIExtraIntertwiner, trace_originalBlockScalarIntertwiner]
  ring

theorem originalIExtraIntertwiner_mem_skewAdjoint
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : ℝ × ℝ) :
    (originalIExtraIntertwiner iota W p).toLinearMap ∈
      skewAdjoint (EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace) := by
  apply originalBlockScalarIntertwiner_mem_skewAdjoint
  · apply star_eq_neg_of_re_eq_zero
    norm_num
  · apply star_eq_neg_of_re_eq_zero
    norm_num
  · apply star_eq_neg_of_re_eq_zero
    norm_num

/-- Transporting the original-space real-form parameterization recovers the
ordered `i*Y5/i*X` block action. -/
theorem transport_originalIExtraIntertwiner
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : ℝ × ℝ) :
    BlockCentralizer.transportCommutant
        (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
        (representationEquivOrderedBlocks W)
        (originalIExtraIntertwiner iota W p) =
      orderedExtraIntertwiner W
        (Complex.I * (p.1 : ℂ)) (Complex.I * (p.2 : ℂ)) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp [BlockCentralizer.transportCommutant_apply,
    originalIExtraIntertwiner, originalBlockScalarIntertwiner,
    orderedExtraIntertwiner]

/-!
## The real-form equivalence
-/

/-- The skew-adjoint, trace-zero part of the actual complex commutant. -/
def SkewTracelessCommutant
    (iota : ProductGroup →* SU6) :=
  {f : Representation.IntertwiningMap
      (euclideanDefiningRestriction iota) (euclideanDefiningRestriction iota) //
    f.toLinearMap ∈
        skewAdjoint (EuclideanRepSpace →ₗ[ℂ] EuclideanRepSpace) ∧
      LinearMap.trace ℂ EuclideanRepSpace f.toLinearMap = 0}

/-- Send two real coefficients to the corresponding anti-Hermitian actual
commutant element. -/
def realExtraParameterization
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (p : ℝ × ℝ) : SkewTracelessCommutant iota :=
  ⟨originalIExtraIntertwiner iota W p,
    originalIExtraIntertwiner_mem_skewAdjoint iota W p,
    originalIExtraIntertwiner_trace_zero iota W p⟩

theorem realExtraParameterization_injective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Injective (realExtraParameterization iota W) := by
  intro p q h
  have hVal := congrArg Subtype.val h
  change originalIExtraIntertwiner iota W p =
    originalIExtraIntertwiner iota W q at hVal
  have hTransport := congrArg
    (BlockCentralizer.transportCommutant
      (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
      (representationEquivOrderedBlocks W)) hVal
  rw [transport_originalIExtraIntertwiner,
    transport_originalIExtraIntertwiner] at hTransport
  have hComplex :
      (Complex.I * (p.1 : ℂ), Complex.I * (p.2 : ℂ)) =
        (Complex.I * (q.1 : ℂ), Complex.I * (q.2 : ℂ)) :=
    orderedExtraIntertwiner_injective W hTransport
  apply Prod.ext
  · have hIm := congrArg (fun z : ℂ × ℂ => z.1.im) hComplex
    simpa using hIm
  · have hIm := congrArg (fun z : ℂ × ℂ => z.2.im) hComplex
    simpa using hIm

theorem realExtraParameterization_surjective
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    Function.Surjective (realExtraParameterization iota W) := by
  rintro ⟨f, hSkew, hTrace⟩
  obtain ⟨p, hp⟩ :=
    (skew_traceless_commutant_eq_iOrderedExtra_unique
      iota W f hSkew hTrace).exists
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change originalIExtraIntertwiner iota W p = f
  apply BlockCentralizer.transportCommutant_injective
    (euclideanDefiningRestriction iota) (orderedBlockRepresentation W)
    (representationEquivOrderedBlocks W)
  rw [transport_originalIExtraIntertwiner]
  exact hp.symm

/-- The anti-Hermitian trace-zero actual commutant has exactly two real
`Y5/X` parameters. -/
def skewTracelessCommutantEquiv
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    (ℝ × ℝ) ≃ SkewTracelessCommutant iota :=
  Equiv.ofBijective (realExtraParameterization iota W)
    ⟨realExtraParameterization_injective iota W,
      realExtraParameterization_surjective iota W⟩

end

end ActualSkewCentralizer
end GUT
