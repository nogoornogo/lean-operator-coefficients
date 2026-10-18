import GUT.SU6.Embeddings.SmoothEmbeddingBridge
import TauCeti.Geometry.Lie.Exponential.Classification
import TauCeti.Geometry.Lie.Exponential.Trotter
import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

open Math

/-!
# Automatic regularity for continuous compact matrix embeddings

This file derives the one-parameter differentiability certificate used by semisimple embedding classification
from continuity alone.  The analytic input is TauCeti's classification of
continuous one-parameter subgroups of finite-dimensional Lie groups.
-/

namespace GUT
namespace ContinuousEmbeddingRegularityBridge

noncomputable section

open Manifold
open scoped Manifold Matrix.Norms.L2Operator
open SpecialUnitaryLieAlgebra

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-! ## Continuous one-parameter subgroups of algebra units -/

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
  [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpace : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

/-- The generator of a continuous one-parameter subgroup of the units of a
finite-dimensional real normed algebra. -/
def unitsGenerator (φ : ContinuousMonoidHom (Multiplicative ℝ) Rˣ) : R :=
  unitsLieAlgebraEquiv
    ((oneParameterSubgroupEquiv (I := 𝓘(ℝ, R)) (G := Rˣ)).symm φ)

/-- Every continuous one-parameter subgroup of finite-dimensional algebra
units is the Banach-algebra exponential of its canonical generator. -/
theorem eq_expUnitHom_unitsGenerator
    (φ : ContinuousMonoidHom (Multiplicative ℝ) Rˣ) :
    φ = TauCeti.expUnitHom (unitsGenerator φ) := by
  rw [unitsGenerator, ← oneParameterSubgroup_eq_expUnitHom]
  exact (oneParameterSubgroupEquiv (I := 𝓘(ℝ, R)) (G := Rˣ)).apply_symm_apply φ |>.symm

/-- The canonical generator is uniquely characterized by the exponential
normal form. -/
theorem unitsGenerator_eq_of_eq_expUnitHom
    (φ : ContinuousMonoidHom (Multiplicative ℝ) Rˣ) (x : R)
    (hφ : φ = TauCeti.expUnitHom x) :
    unitsGenerator φ = x := by
  apply TauCeti.expUnitHom_injective
  rw [← hφ]
  exact (eq_expUnitHom_unitsGenerator φ).symm

/-- The Trotter product formula expressed directly in the unit group of a
finite-dimensional real normed algebra. -/
theorem tendsto_expUnit_trotter (x y : R) (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (TauCeti.expUnit ((t / (n : ℝ)) • x) *
          TauCeti.expUnit ((t / (n : ℝ)) • y)) ^ n)
      Filter.atTop
      (nhds (TauCeti.expUnit (t • (x + y)))) := by
  let L := unitsLieAlgebraEquiv (R := R)
  have h := tendsto_lieExp_smul_mul_lieExp_smul_pow
    (I := 𝓘(ℝ, R)) (G := Rˣ) (L.symm x) (L.symm y) t
  simpa only [lieExp_eq_expUnit, L, LinearEquiv.apply_symm_apply,
    map_smul, map_add] using h

/-! ## Matrix one-parameter subgroups attached to the embedding -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The canonical continuous inclusion from a special unitary matrix group
into the units of its ambient matrix algebra. -/
def specialUnitaryToUnits :
    Matrix.specialUnitaryGroup n ℂ →ₜ* (Matrix n n ℂ)ˣ where
  toMonoidHom := (Matrix.specialUnitaryGroup n ℂ).subtype.toHomUnits
  continuous_toFun := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · change Continuous (fun U : Matrix.specialUnitaryGroup n ℂ =>
        ((U⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ))
      fun_prop

@[simp]
theorem specialUnitaryToUnits_coe
    (U : Matrix.specialUnitaryGroup n ℂ) :
    ((specialUnitaryToUnits U : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = U :=
  rfl

/-- A compact-real-form direction exponentiated along real time, bundled as
a continuous one-parameter subgroup of `SU(n)`. -/
def compactOneParameter (X : CompactRealForm n) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.specialUnitaryGroup n ℂ) where
  toFun t := CompactRealForm.expSpecialUnitary (Multiplicative.toAdd t • X)
  map_one' := by simp
  map_mul' s t := by
    simpa using CompactRealForm.expSpecialUnitary_real_smul_add X
      (Multiplicative.toAdd s) (Multiplicative.toAdd t)
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : Multiplicative ℝ =>
      NormedSpace.exp
        (Multiplicative.toAdd t • (X : Matrix n n ℂ)))
    exact (TauCeti.contDiff_exp_smul (X : Matrix n n ℂ)).continuous.comp
      continuous_toAdd

/-- The matrix Trotter sequence stays in `SU(n)` and converges there to the
exponential of the sum. -/
theorem tendsto_compact_trotter (X Y : CompactRealForm n) (t : ℝ) :
    Filter.Tendsto
      (fun k : ℕ =>
        (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • X) *
          CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Y)) ^ k)
      Filter.atTop
      (nhds (CompactRealForm.expSpecialUnitary (t • (X + Y)))) := by
  rw [tendsto_subtype_rng]
  change Filter.Tendsto
    (fun k : ℕ =>
      (NormedSpace.exp ((t / (k : ℝ)) • (X : Matrix n n ℂ)) *
        NormedSpace.exp ((t / (k : ℝ)) • (Y : Matrix n n ℂ))) ^ k)
    Filter.atTop
    (nhds
      (NormedSpace.exp
        (t • ((X : Matrix n n ℂ) + (Y : Matrix n n ℂ)))))
  have hUnits := tendsto_expUnit_trotter
    (R := Matrix n n ℂ) (X : Matrix n n ℂ) (Y : Matrix n n ℂ) t
  have hval : Continuous
      (fun u : (Matrix n n ℂ)ˣ => u.val) :=
    Units.continuous_val
  have hMatrix :
      Filter.Tendsto
        (fun k : ℕ =>
          ((TauCeti.expUnit ((t / (k : ℝ)) • (X : Matrix n n ℂ)) *
            TauCeti.expUnit ((t / (k : ℝ)) • (Y : Matrix n n ℂ))) ^ k).val)
        Filter.atTop
        (nhds
          (TauCeti.expUnit
            (t • ((X : Matrix n n ℂ) + (Y : Matrix n n ℂ)))).val) := by
    refine (hval.continuousAt.tendsto.comp hUnits).congr' ?_
    exact Filter.Eventually.of_forall (fun _ => rfl)
  simpa only [Units.val_pow_eq_pow_val, Units.val_mul,
    TauCeti.expUnit_coe] using hMatrix

open CompactEmbeddingClassification EmbeddingDifferentialBridge
  SmoothEmbeddingBridge

attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup
  NormedSpace.toModule PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- The product exponential curve in the source group. -/
def sourceOneParameter (Z : SourceLie) :
    ContinuousMonoidHom (Multiplicative ℝ) ProductGroup :=
  (compactOneParameter Z.1).prod (compactOneParameter Z.2)

/-- The product of the two compact matrix Trotter sequences converges in the
source group. -/
theorem tendsto_source_trotter (Z W : SourceLie) (t : ℝ) :
    Filter.Tendsto
      (fun k : ℕ =>
        ((CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.1) *
              CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.1)) ^ k,
          (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.2) *
              CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.2)) ^ k))
      Filter.atTop
      (nhds
        (CompactRealForm.expSpecialUnitary (t • (Z.1 + W.1)),
          CompactRealForm.expSpecialUnitary (t • (Z.2 + W.2)))) :=
  (tendsto_compact_trotter Z.1 W.1 t).prodMk_nhds
    (tendsto_compact_trotter Z.2 W.2 t)

/-- A source exponential curve, mapped through a continuous embedding and
then included in the units of the ambient `6 x 6` matrix algebra. -/
def embeddingOneParameter (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    ContinuousMonoidHom (Multiplicative ℝ) Matrix6ˣ :=
  specialUnitaryToUnits.comp (iota.comp (sourceOneParameter Z))

/-- The ambient matrix generator of the image of a source Lie-algebra
direction.  Its linearity in `Z` is proved below using the Trotter formula. -/
def embeddingGenerator (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    Matrix6 :=
  unitsGenerator (embeddingOneParameter iota Z)

/-- The image of every source exponential line is the matrix exponential of
its canonical generator. -/
theorem embeddingOneParameter_eq_expUnitHom
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    embeddingOneParameter iota Z =
      TauCeti.expUnitHom (embeddingGenerator iota Z) :=
  eq_expUnitHom_unitsGenerator _

/-- Pointwise exponential form of the embedded source one-parameter
subgroup. -/
theorem embedding_exp_eq_expUnit
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) (t : ℝ) :
    specialUnitaryToUnits
        (iota
          (CompactRealForm.expSpecialUnitary (t • Z.1),
            CompactRealForm.expSpecialUnitary (t • Z.2))) =
      TauCeti.expUnit (t • embeddingGenerator iota Z) := by
  change embeddingOneParameter iota Z (Multiplicative.ofAdd t) = _
  simpa only [TauCeti.expUnitHom_apply] using
    DFunLike.congr_fun (embeddingOneParameter_eq_expUnitHom iota Z)
      (Multiplicative.ofAdd t)

/-- Mapping a source Trotter term through the embedding gives the target
Trotter term for the two canonical generators. -/
theorem embedding_trotter_term
    (iota : ProductGroup →ₜ* SU6) (Z W : SourceLie) (t : ℝ) (k : ℕ) :
    specialUnitaryToUnits
        (iota
          ((CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.1) *
                CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.1)) ^ k,
            (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.2) *
                CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.2)) ^ k)) =
      (TauCeti.expUnit ((t / (k : ℝ)) • embeddingGenerator iota Z) *
        TauCeti.expUnit ((t / (k : ℝ)) • embeddingGenerator iota W)) ^ k := by
  change (specialUnitaryToUnits.comp iota)
      (((CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.1),
            CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.2)) *
          (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.1),
            CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.2))) ^ k) = _
  rw [map_pow, map_mul]
  change (specialUnitaryToUnits
          (iota
            (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.1),
              CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.2))) *
        specialUnitaryToUnits
          (iota
            (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.1),
              CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.2)))) ^ k = _
  rw [embedding_exp_eq_expUnit, embedding_exp_eq_expUnit]

/-- The target Trotter sequence also converges to the image of the source
sum, by continuity of the original group embedding. -/
theorem tendsto_embedding_trotter
    (iota : ProductGroup →ₜ* SU6) (Z W : SourceLie) (t : ℝ) :
    Filter.Tendsto
      (fun k : ℕ =>
        (TauCeti.expUnit ((t / (k : ℝ)) • embeddingGenerator iota Z) *
          TauCeti.expUnit ((t / (k : ℝ)) • embeddingGenerator iota W)) ^ k)
      Filter.atTop
      (nhds (TauCeti.expUnit (t • embeddingGenerator iota (Z + W)))) := by
  let F : ProductGroup →ₜ* Matrix6ˣ := specialUnitaryToUnits.comp iota
  have hSource := tendsto_source_trotter Z W t
  have hImage := F.continuous.continuousAt.tendsto.comp hSource
  have hLimit :
      F
          (CompactRealForm.expSpecialUnitary (t • (Z.1 + W.1)),
            CompactRealForm.expSpecialUnitary (t • (Z.2 + W.2))) =
        TauCeti.expUnit (t • embeddingGenerator iota (Z + W)) := by
    change specialUnitaryToUnits
        (iota
          (CompactRealForm.expSpecialUnitary (t • (Z.1 + W.1)),
            CompactRealForm.expSpecialUnitary (t • (Z.2 + W.2)))) = _
    simpa using embedding_exp_eq_expUnit iota (Z + W) t
  have hLimit' :
      F.toContinuousMap
          (CompactRealForm.expSpecialUnitary (t • (Z.1 + W.1)),
            CompactRealForm.expSpecialUnitary (t • (Z.2 + W.2))) =
        TauCeti.expUnit (t • embeddingGenerator iota (Z + W)) :=
    hLimit
  rw [hLimit'] at hImage
  refine hImage.congr' (Filter.Eventually.of_forall fun k => ?_)
  change specialUnitaryToUnits
      (iota
        ((CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.1) *
              CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.1)) ^ k,
          (CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • Z.2) *
              CompactRealForm.expSpecialUnitary ((t / (k : ℝ)) • W.2)) ^ k)) = _
  exact embedding_trotter_term iota Z W t k

/-- Trotter-limit uniqueness identifies the exponential of the image of a
source sum with the exponential of the sum of the two target generators. -/
theorem expUnit_embeddingGenerator_add
    (iota : ProductGroup →ₜ* SU6) (Z W : SourceLie) (t : ℝ) :
    TauCeti.expUnit (t • embeddingGenerator iota (Z + W)) =
      TauCeti.expUnit
        (t • (embeddingGenerator iota Z + embeddingGenerator iota W)) :=
  tendsto_nhds_unique
    (tendsto_embedding_trotter iota Z W t)
    (tendsto_expUnit_trotter
      (embeddingGenerator iota Z) (embeddingGenerator iota W) t)

/-- The canonical target generator is additive in the source Lie-algebra
direction. -/
theorem embeddingGenerator_add
    (iota : ProductGroup →ₜ* SU6) (Z W : SourceLie) :
    embeddingGenerator iota (Z + W) =
      embeddingGenerator iota Z + embeddingGenerator iota W := by
  apply TauCeti.expUnitHom_injective
  apply ContinuousMonoidHom.ext
  intro t
  calc
    TauCeti.expUnitHom (embeddingGenerator iota (Z + W)) t =
        TauCeti.expUnit
          (Multiplicative.toAdd t • embeddingGenerator iota (Z + W)) := by
      rw [← ofAdd_toAdd t]
      exact TauCeti.expUnitHom_apply _ _
    _ = TauCeti.expUnit
          (Multiplicative.toAdd t •
            (embeddingGenerator iota Z + embeddingGenerator iota W)) :=
      expUnit_embeddingGenerator_add iota Z W (Multiplicative.toAdd t)
    _ = TauCeti.expUnitHom
          (embeddingGenerator iota Z + embeddingGenerator iota W) t := by
      rw [← ofAdd_toAdd t]
      exact (TauCeti.expUnitHom_apply _ _).symm

/-- Continuity of the group homomorphism is enough to obtain the derivative
of its image along each source exponential line. -/
theorem embedding_curve_hasDerivAt_zero
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    HasDerivAt
      (fun t : ℝ =>
        ((iota
          (CompactRealForm.expSpecialUnitary (t • Z.1),
            CompactRealForm.expSpecialUnitary (t • Z.2)) : SU6) : Matrix6))
      (embeddingGenerator iota Z) 0 := by
  have h := TauCeti.hasDerivAt_expUnitHom_val_zero
    (embeddingGenerator iota Z)
  rw [← embeddingOneParameter_eq_expUnitHom iota Z] at h
  exact h

/-- Reparameterizing a source exponential line scales its canonical target
generator. -/
theorem embeddingGenerator_smul
    (iota : ProductGroup →ₜ* SU6) (a : ℝ) (Z : SourceLie) :
    embeddingGenerator iota (a • Z) =
      a • embeddingGenerator iota Z := by
  apply unitsGenerator_eq_of_eq_expUnitHom
  apply ContinuousMonoidHom.ext
  intro t
  have hsource :
      embeddingOneParameter iota (a • Z) t =
        embeddingOneParameter iota Z
          (Multiplicative.ofAdd (a * Multiplicative.toAdd t)) := by
    change specialUnitaryToUnits
        (iota
          (CompactRealForm.expSpecialUnitary
              (Multiplicative.toAdd t • (a • Z.1)),
            CompactRealForm.expSpecialUnitary
              (Multiplicative.toAdd t • (a • Z.2)))) =
      specialUnitaryToUnits
        (iota
          (CompactRealForm.expSpecialUnitary
              (Multiplicative.toAdd
                  (Multiplicative.ofAdd (a * Multiplicative.toAdd t)) • Z.1),
            CompactRealForm.expSpecialUnitary
              (Multiplicative.toAdd
                  (Multiplicative.ofAdd (a * Multiplicative.toAdd t)) • Z.2)))
    simp [smul_smul, mul_comm]
  rw [hsource, embeddingOneParameter_eq_expUnitHom]
  have hrhs :
      TauCeti.expUnitHom (a • embeddingGenerator iota Z) t =
        TauCeti.expUnit
          (Multiplicative.toAdd t • (a • embeddingGenerator iota Z)) := by
    calc
      _ = TauCeti.expUnitHom (a • embeddingGenerator iota Z)
          (Multiplicative.ofAdd (Multiplicative.toAdd t)) := by
            rw [ofAdd_toAdd]
      _ = _ := TauCeti.expUnitHom_apply _ _
  rw [hrhs]
  simp [smul_smul, mul_comm]

set_option linter.style.haveILetI false in
/-- The generator of an embedded source one-parameter subgroup is
skew-adjoint because the whole curve lies in `SU(6)`. -/
theorem embeddingGenerator_mem_skewAdjoint
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    embeddingGenerator iota Z ∈ skewAdjoint Matrix6 := by
  letI hNormedAdd : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAdd.toAddCommGroup
  let f : ℝ → Matrix6 := fun t =>
    ((iota
      (CompactRealForm.expSpecialUnitary (t • Z.1),
        CompactRealForm.expSpecialUnitary (t • Z.2)) : SU6) : Matrix6)
  have hCurve : HasDerivAt f (embeddingGenerator iota Z) 0 :=
    embedding_curve_hasDerivAt_zero iota Z
  have hf0 : f 0 = 1 := by
    dsimp [f]
    rw [zero_smul, CompactRealForm.expSpecialUnitary_zero,
      zero_smul, CompactRealForm.expSpecialUnitary_zero]
    rw [show ((1 : SU3), (1 : SU2)) = (1 : ProductGroup) by rfl,
      map_one]
    rfl
  have hProduct := hCurve.star.mul hCurve
  have hConstant : HasDerivAt (fun t : ℝ => star (f t) * f t) 0 0 := by
    apply (hasDerivAt_const (x := (0 : ℝ))
      (c := (1 : Matrix6))).congr_of_eventuallyEq
    filter_upwards [] with t
    exact Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup
        ((iota
          (CompactRealForm.expSpecialUnitary (t • Z.1),
            CompactRealForm.expSpecialUnitary (t • Z.2))).property))
  have hZero := hProduct.unique hConstant
  simp only [hf0, star_one, mul_one, one_mul] at hZero
  rw [skewAdjoint.mem_iff]
  apply eq_neg_of_add_eq_zero_left
  exact hZero

set_option linter.style.haveILetI false in
/-- The generator is traceless because the determinant of the embedded curve
is constantly one. -/
theorem embeddingGenerator_trace_eq_zero
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    Matrix.trace (embeddingGenerator iota Z) = 0 := by
  letI hNormedAdd : NormedAddCommGroup Matrix6 :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : AddCommGroup Matrix6 := hNormedAdd.toAddCommGroup
  let f : ℝ → Matrix6 := fun t =>
    ((iota
      (CompactRealForm.expSpecialUnitary (t • Z.1),
        CompactRealForm.expSpecialUnitary (t • Z.2)) : SU6) : Matrix6)
  have hCurve : HasDerivAt f (embeddingGenerator iota Z) 0 :=
    embedding_curve_hasDerivAt_zero iota Z
  have hDetReal :=
    (MatrixDeterminantExponential.hasFDerivAt_det_one
      (n := Fin 6)).restrictScalars ℝ
  have hDetCurve := hDetReal.comp_hasDerivAt_of_eq 0 hCurve (by
    dsimp [f]
    rw [zero_smul, CompactRealForm.expSpecialUnitary_zero,
      zero_smul, CompactRealForm.expSpecialUnitary_zero]
    rw [show ((1 : SU3), (1 : SU2)) = (1 : ProductGroup) by rfl,
      map_one]
    rfl)
  have hConstant : HasDerivAt (fun t : ℝ => Matrix.det (f t)) 0 0 := by
    apply (hasDerivAt_const (x := (0 : ℝ))
      (c := (1 : ℂ))).congr_of_eventuallyEq
    filter_upwards [] with t
    change Matrix.det
      (((iota
        (CompactRealForm.expSpecialUnitary (t • Z.1),
          CompactRealForm.expSpecialUnitary (t • Z.2)) : SU6) : Matrix6)) = 1
    exact
      (iota
        (CompactRealForm.expSpecialUnitary (t • Z.1),
          CompactRealForm.expSpecialUnitary (t • Z.2))).property.2
  simpa using hDetCurve.unique hConstant

/-- The canonical ambient generator, corestricted to the compact target Lie
algebra. -/
def embeddingTangentValue
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    CompactRealForm (Fin 6) where
  toSpecialLinear :=
    ⟨embeddingGenerator iota Z, embeddingGenerator_trace_eq_zero iota Z⟩
  skewAdjoint := embeddingGenerator_mem_skewAdjoint iota Z

@[simp]
theorem coe_embeddingTangentValue
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    (embeddingTangentValue iota Z : Matrix6) = embeddingGenerator iota Z :=
  rfl

/-- The automatic one-parameter generator is a real-linear map into
`su(6)`. -/
def embeddingDifferential (iota : ProductGroup →ₜ* SU6) :
    SourceLie →ₗ[ℝ] CompactRealForm (Fin 6) where
  toFun := embeddingTangentValue iota
  map_add' := by
    intro Z W
    apply CompactRealForm.ext
    apply Subtype.ext
    exact embeddingGenerator_add iota Z W
  map_smul' := by
    intro a Z
    apply CompactRealForm.ext
    apply Subtype.ext
    exact embeddingGenerator_smul iota a Z

/-- The same canonical generator as a real-linear map into the ambient matrix
algebra. -/
def embeddingGeneratorLinear (iota : ProductGroup →ₜ* SU6) :
    SourceLie →ₗ[ℝ] Matrix6 where
  toFun := embeddingGenerator iota
  map_add' := embeddingGenerator_add iota
  map_smul' := embeddingGenerator_smul iota

/-- Finite dimensionality makes the ambient generator map continuous. -/
def embeddingGeneratorContinuousLinear (iota : ProductGroup →ₜ* SU6) :
    SourceLie →L[ℝ] Matrix6 :=
  { embeddingGeneratorLinear iota with
    cont := LinearMap.continuous_of_finiteDimensional
      (embeddingGeneratorLinear iota) }

@[simp]
theorem embeddingGeneratorContinuousLinear_apply
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    embeddingGeneratorContinuousLinear iota Z = embeddingGenerator iota Z :=
  rfl

@[simp]
theorem embeddingGenerator_zero (iota : ProductGroup →ₜ* SU6) :
    embeddingGenerator iota 0 = 0 :=
  (embeddingGeneratorLinear iota).map_zero

/-- In exponential source coordinates, a continuous compact matrix-group
homomorphism is exactly the ambient matrix exponential of its canonical
linear generator. -/
theorem exponentialChartMap_eq_exp
    (iota : ProductGroup →ₜ* SU6) (Z : SourceLie) :
    exponentialChartMap (iota : ProductGroup →* SU6) Z =
      NormedSpace.exp (embeddingGenerator iota Z) := by
  have h := congrArg (fun U : Matrix6ˣ => (U : Matrix6))
    (embedding_exp_eq_expUnit iota Z 1)
  rw [TauCeti.expUnit_coe] at h
  have h' :
      ((iota
        (CompactRealForm.expSpecialUnitary Z.1,
          CompactRealForm.expSpecialUnitary Z.2) : SU6) : Matrix6) =
        NormedSpace.exp (embeddingGenerator iota Z) := by
    simpa only [one_smul, specialUnitaryToUnits_coe] using h
  unfold exponentialChartMap
  rw [show
    (iota : ProductGroup →* SU6)
        (CompactRealForm.expSpecialUnitary Z.1,
          CompactRealForm.expSpecialUnitary Z.2) =
      iota
        (CompactRealForm.expSpecialUnitary Z.1,
          CompactRealForm.expSpecialUnitary Z.2) from rfl]
  exact h'

/-- Automatic regularity in the stronger Fréchet form used by the original E
assembly interface. -/
theorem exponentialChartMap_hasFDerivAt_zero
    (iota : ProductGroup →ₜ* SU6) :
    HasFDerivAt
      (exponentialChartMap (iota : ProductGroup →* SU6))
      (embeddingGeneratorContinuousLinear iota) 0 := by
  have hExpAt :
      HasFDerivAt (NormedSpace.exp : Matrix6 → Matrix6)
        (1 : Matrix6 →L[ℝ] Matrix6)
        (embeddingGeneratorContinuousLinear iota 0) := by
    simpa using (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix6))
  have hExp :=
    hExpAt.comp 0
      (embeddingGeneratorContinuousLinear iota).hasFDerivAt
  rw [show exponentialChartMap (iota : ProductGroup →* SU6) =
      fun Z => NormedSpace.exp (embeddingGeneratorContinuousLinear iota Z) by
    funext Z
    exact exponentialChartMap_eq_exp iota Z]
  convert hExp using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro Z
    rfl

theorem exponentialChartMap_differentiableAt
    (iota : ProductGroup →ₜ* SU6) :
    DifferentiableAt ℝ
      (exponentialChartMap (iota : ProductGroup →* SU6)) 0 :=
  (exponentialChartMap_hasFDerivAt_zero iota).differentiableAt

/-- Every continuous compact matrix-group embedding supplies the exact
one-parameter differentiability certificate consumed by semisimple embedding classification. -/
def toOneParameterDifferentiableEmbedding
    (iota : ProductGroup →ₜ* SU6) :
    OneParameterDifferentiableEmbedding
      (iota : ProductGroup →* SU6) where
  differential := embeddingDifferential iota
  derivative_at_zero := by
    intro X Y
    exact embedding_curve_hasDerivAt_zero iota (X, Y)

/-- A continuous injective embedding with a nontrivial commuting circle has
the full classified semisimple embedding classification decomposition. -/
theorem continuousInjectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    Nonempty (WeakDoubletEmbeddingClassification.ClassifiedWeakDoubletDecomposition
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6))) :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_oneParameterDifferentiableEmbedding
    iota hInjective Y hCommute hNontrivial
      (toOneParameterDifferentiableEmbedding iota)

/-- Numerical block classification for the same continuity-only semisimple embedding classification input. -/
theorem continuousInjectiveEmbedding_with_hypercharge_has_weakDoubletBranch
    (iota : ProductGroup →ₜ* SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (hNontrivial : Y ≠ 1) :
    ∃ B : LowDimensionalIrreps.SixDimensionalBlockDecomposition,
      B.toBranchCounts.IsWeakDoubletBlock :=
  EmbeddingDifferentialBridge.injectiveEmbedding_with_hypercharge_has_weakDoubletBranch_of_oneParameterDifferentiableEmbedding
    iota hInjective Y hCommute hNontrivial
      (toOneParameterDifferentiableEmbedding iota)

end
end ContinuousEmbeddingRegularityBridge
end GUT
