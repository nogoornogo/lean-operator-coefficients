import Math.LieGroups.Matrix.MatrixDeterminantExponential
import GUT.SU6.Embeddings.SpecialUnitaryExponential
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

open Math

/-!
# The compact real form and its exponential into `SU(n)`

This file realizes the elementary matrix part of the semisimple embedding classification analytic bridge.  A
compact special-linear Lie element is a traceless complex matrix which is
skew-Hermitian.  Its matrix exponential is proved to be special unitary.  The
determinant-one proof uses the checked determinant-exponential identity from
`MatrixDeterminantExponential`.
-/

namespace GUT
namespace SpecialUnitaryLieAlgebra

open CompactEmbeddingClassification ExponentialRepresentationBridge
  HighestWeightBridge

noncomputable section

open NormedSpace
open scoped Matrix.Norms.L2Operator

universe u

section General

variable (n : Type u) [Fintype n] [DecidableEq n]

/-- The compact real form `su(n)`, represented inside the complex
trace-zero matrix Lie algebra. -/
structure CompactRealForm where
  toSpecialLinear : LieAlgebra.SpecialLinear.sl n ℂ
  skewAdjoint :
    (toSpecialLinear.1 : Matrix n n ℂ) ∈
      skewAdjoint (Matrix n n ℂ)

namespace CompactRealForm

variable {n}

instance : Coe (CompactRealForm n) (LieAlgebra.SpecialLinear.sl n ℂ) :=
  ⟨toSpecialLinear⟩

instance : Coe (CompactRealForm n) (Matrix n n ℂ) :=
  ⟨fun X ↦ X.toSpecialLinear.1⟩

/-- Real scaling preserves both tracelessness and skew-adjointness.  This is
the scalar operation used to form one-parameter subgroups `t |-> exp(tX)`. -/
instance : SMul ℝ (CompactRealForm n) where
  smul t X :=
    { toSpecialLinear := (t : ℂ) • X.toSpecialLinear
      skewAdjoint := by
        simpa [Complex.real_smul] using
          (skewAdjoint.smul_mem t X.skewAdjoint) }

@[simp]
theorem coe_real_smul (t : ℝ) (X : CompactRealForm n) :
    ((t • X : CompactRealForm n) : Matrix n n ℂ) =
      (t : ℂ) • (X : Matrix n n ℂ) :=
  rfl

@[ext]
theorem ext {X Y : CompactRealForm n}
    (h : X.toSpecialLinear = Y.toSpecialLinear) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

@[simp]
theorem one_smul_compactRealForm (X : CompactRealForm n) :
    (1 : ℝ) • X = X := by
  apply ext
  apply Subtype.ext
  simp

instance : Zero (CompactRealForm n) where
  zero := { toSpecialLinear := 0, skewAdjoint := by simp }

instance : Add (CompactRealForm n) where
  add X Y :=
    { toSpecialLinear := X.toSpecialLinear + Y.toSpecialLinear
      skewAdjoint := (_root_.skewAdjoint (Matrix n n ℂ)).add_mem
        X.skewAdjoint Y.skewAdjoint }

instance : Neg (CompactRealForm n) where
  neg X :=
    { toSpecialLinear := -X.toSpecialLinear
      skewAdjoint := (_root_.skewAdjoint (Matrix n n ℂ)).neg_mem
        X.skewAdjoint }

instance : Sub (CompactRealForm n) where
  sub X Y := X + -Y

private theorem toSpecialLinear_injective :
    Function.Injective (toSpecialLinear : CompactRealForm n →
      LieAlgebra.SpecialLinear.sl n ℂ) := by
  intro X Y h
  exact ext h

/-- The compact real form is an additive subgroup of `sl(n,C)`. -/
instance : AddCommGroup (CompactRealForm n) where
  add_assoc X Y Z := toSpecialLinear_injective
    (add_assoc X.toSpecialLinear Y.toSpecialLinear Z.toSpecialLinear)
  zero_add X := toSpecialLinear_injective (zero_add X.toSpecialLinear)
  add_zero X := toSpecialLinear_injective (add_zero X.toSpecialLinear)
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  neg_add_cancel X := toSpecialLinear_injective
    (neg_add_cancel X.toSpecialLinear)
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl
  sub_eq_add_neg := fun _ _ => rfl
  add_comm X Y := toSpecialLinear_injective
    (add_comm X.toSpecialLinear Y.toSpecialLinear)

@[simp]
theorem toSpecialLinear_zero :
    (0 : CompactRealForm n).toSpecialLinear = 0 := rfl

@[simp]
theorem toSpecialLinear_add (X Y : CompactRealForm n) :
    (X + Y).toSpecialLinear = X.toSpecialLinear + Y.toSpecialLinear := rfl

@[simp]
theorem toSpecialLinear_neg (X : CompactRealForm n) :
    (-X).toSpecialLinear = -X.toSpecialLinear := rfl

@[simp]
theorem toSpecialLinear_sub (X Y : CompactRealForm n) :
    (X - Y).toSpecialLinear = X.toSpecialLinear - Y.toSpecialLinear := rfl

/-- Real scalar multiplication makes the compact real form a real vector
space, compatibly with its inclusion into `sl(n,C)`. -/
instance : Module ℝ (CompactRealForm n) :=
  let f : CompactRealForm n →+ LieAlgebra.SpecialLinear.sl n ℂ :=
    { toFun := toSpecialLinear
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  toSpecialLinear_injective.module ℝ f (fun _ _ => rfl)

@[simp]
theorem toSpecialLinear_real_smul (t : ℝ) (X : CompactRealForm n) :
    (t • X).toSpecialLinear = (t : ℂ) • X.toSpecialLinear := rfl

/-!
### Canonical finite-dimensional normed structure

The compact real form carries the norm induced by its faithful inclusion in
the ambient complex matrix algebra.  This concrete choice lets the elementary
matrix derivative of the adjoint curve be transported back to `su(n)`.
-/

/-- The faithful real-linear inclusion of the compact real form into complex
matrices. -/
def toMatrixRealLinear : CompactRealForm n →ₗ[ℝ] Matrix n n ℂ where
  toFun X := X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toMatrixRealLinear_injective :
    Function.Injective (toMatrixRealLinear (n := n)) := by
  intro X Y h
  apply ext
  exact Subtype.ext h

/-- The matrix norm restricted to the compact real form. -/
instance : NormedAddCommGroup (CompactRealForm n) :=
  NormedAddCommGroup.induced _ _ (toMatrixRealLinear (n := n))
    toMatrixRealLinear_injective

/-- The induced norm is compatible with the real vector-space structure. -/
instance : NormedSpace ℝ (CompactRealForm n) :=
  NormedSpace.induced ℝ _ _ (toMatrixRealLinear (n := n))

/-- The compact real form is finite-dimensional over the reals. -/
instance : FiniteDimensional ℝ (CompactRealForm n) :=
  FiniteDimensional.of_injective (toMatrixRealLinear (n := n))
    toMatrixRealLinear_injective

attribute [local instance] LieRing.ofAssociativeRing

/-- The matrix commutator of two skew-adjoint traceless matrices is again
skew-adjoint and traceless. -/
instance : Bracket (CompactRealForm n) (CompactRealForm n) where
  bracket X Y :=
    { toSpecialLinear := ⁅X.toSpecialLinear, Y.toSpecialLinear⁆
      skewAdjoint := by
        have hX := X.skewAdjoint
        have hY := Y.skewAdjoint
        rw [_root_.skewAdjoint.mem_iff] at hX hY ⊢
        change star
          (⁅(X.toSpecialLinear.1 : Matrix n n ℂ),
              (Y.toSpecialLinear.1 : Matrix n n ℂ)⁆) =
            -⁅(X.toSpecialLinear.1 : Matrix n n ℂ),
              (Y.toSpecialLinear.1 : Matrix n n ℂ)⁆
        simp only [LieRing.of_associative_ring_bracket, star_sub, star_mul,
          hX, hY]
        noncomm_ring }

/-- The compact real form with its matrix commutator is a real Lie ring. -/
instance : LieRing (CompactRealForm n) where
  add_lie X Y Z := toSpecialLinear_injective
    (add_lie X.toSpecialLinear Y.toSpecialLinear Z.toSpecialLinear)
  lie_add X Y Z := toSpecialLinear_injective
    (lie_add X.toSpecialLinear Y.toSpecialLinear Z.toSpecialLinear)
  lie_self X := toSpecialLinear_injective (lie_self X.toSpecialLinear)
  leibniz_lie X Y Z := toSpecialLinear_injective
    (leibniz_lie X.toSpecialLinear Y.toSpecialLinear Z.toSpecialLinear)

@[simp]
theorem toSpecialLinear_lie (X Y : CompactRealForm n) :
    ⁅X, Y⁆.toSpecialLinear =
      ⁅X.toSpecialLinear, Y.toSpecialLinear⁆ := rfl

/-- The matrix bracket is bilinear over the real scalars. -/
instance : LieAlgebra ℝ (CompactRealForm n) where
  lie_smul t X Y := by
    apply toSpecialLinear_injective
    change ⁅X.toSpecialLinear, (t : ℂ) • Y.toSpecialLinear⁆ =
      (t : ℂ) • ⁅X.toSpecialLinear, Y.toSpecialLinear⁆
    exact lie_smul (t : ℂ) X.toSpecialLinear Y.toSpecialLinear

/-- Inclusion of the compact real form into the real scalar restriction of
`sl(n,C)`, as a real Lie-algebra homomorphism. -/
def toSpecialLinearRealLieHom :
    CompactRealForm n →ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (LieAlgebra.SpecialLinear.sl n ℂ) where
  toFun := toSpecialLinear
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  map_lie' := rfl

/-- Conjugation by a special unitary matrix preserves the compact real form. -/
def conjugate (g : Matrix.specialUnitaryGroup n ℂ)
    (Y : CompactRealForm n) : CompactRealForm n where
  toSpecialLinear :=
    ⟨(g : Matrix n n ℂ) * (Y : Matrix n n ℂ) *
        ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ), by
      change Matrix.trace
        ((g : Matrix n n ℂ) * (Y : Matrix n n ℂ) *
          ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ)) = 0
      rw [Matrix.trace_mul_cycle]
      have hTrace := Y.toSpecialLinear.2
      change Matrix.trace (Y : Matrix n n ℂ) = 0 at hTrace
      have hInv := congrArg Subtype.val (inv_mul_cancel g)
      change
        ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ) *
            (g : Matrix n n ℂ) = 1 at hInv
      rw [hInv, one_mul, hTrace]⟩
  skewAdjoint := by
    have hY := Y.skewAdjoint
    rw [_root_.skewAdjoint.mem_iff] at hY ⊢
    simp only [star_mul, ← Matrix.specialUnitaryGroup.coe_star,
      Matrix.star_eq_inv, inv_inv, hY]
    noncomm_ring

@[simp]
theorem coe_conjugate (g : Matrix.specialUnitaryGroup n ℂ)
    (Y : CompactRealForm n) :
    (conjugate g Y : Matrix n n ℂ) =
      (g : Matrix n n ℂ) * (Y : Matrix n n ℂ) *
        ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ) :=
  rfl

/-!
### Complexification of the compact real form

Every traceless complex matrix is the sum of its skew-adjoint part and `i`
times another skew-adjoint traceless matrix.  This realizes, at the linear
level needed below, the standard fact that `sl(n,C)` is the complexification
of `su(n)`.
-/

/-- The skew-adjoint part of a traceless matrix remains traceless. -/
def skewPart (Z : LieAlgebra.SpecialLinear.sl n ℂ) : CompactRealForm n where
  toSpecialLinear :=
    ⟨(skewAdjointPart ℝ (Z.1 : Matrix n n ℂ) : Matrix n n ℂ), by
      have hZ : Matrix.trace (Z.1 : Matrix n n ℂ) = 0 := Z.2
      have hStar : Matrix.trace (star (Z.1 : Matrix n n ℂ)) = 0 := by
        rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hZ, star_zero]
      change Matrix.trace
        (skewAdjointPart ℝ (Z.1 : Matrix n n ℂ) : Matrix n n ℂ) = 0
      simp [skewAdjointPart_apply_coe, hZ, hStar]⟩
  skewAdjoint := (skewAdjointPart ℝ (Z.1 : Matrix n n ℂ)).2

/-- Multiplying the self-adjoint part of a traceless matrix by `-i` gives a
second element of the compact real form. -/
def selfPart (Z : LieAlgebra.SpecialLinear.sl n ℂ) : CompactRealForm n where
  toSpecialLinear :=
    ⟨(-Complex.I) •
        (selfAdjointPart ℝ (Z.1 : Matrix n n ℂ) : Matrix n n ℂ), by
      have hZ : Matrix.trace (Z.1 : Matrix n n ℂ) = 0 := Z.2
      have hStar : Matrix.trace (star (Z.1 : Matrix n n ℂ)) = 0 := by
        rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, hZ, star_zero]
      change Matrix.trace
        ((-Complex.I) •
          (selfAdjointPart ℝ (Z.1 : Matrix n n ℂ) : Matrix n n ℂ)) = 0
      simp [selfAdjointPart_apply_coe, hZ, hStar]⟩
  skewAdjoint := by
    exact (selfAdjointPart ℝ (Z.1 : Matrix n n ℂ)).2.smul_mem_skewAdjoint
      ((_root_.skewAdjoint ℂ).neg_mem Complex.I_mem_skewAdjoint)

/-- Explicit complexification decomposition `Z = K + iS`, with both `K`
and `S` in the compact real form. -/
theorem skewPart_add_I_smul_selfPart
    (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    (skewPart Z).toSpecialLinear +
        Complex.I • (selfPart Z).toSpecialLinear = Z := by
  apply Subtype.ext
  let K : Matrix n n ℂ :=
    (skewAdjointPart ℝ (Z.1 : Matrix n n ℂ) : Matrix n n ℂ)
  let H : Matrix n n ℂ :=
    (selfAdjointPart ℝ (Z.1 : Matrix n n ℂ) : Matrix n n ℂ)
  change K + Complex.I • ((-Complex.I) • H) = Z.1
  calc
    K + Complex.I • ((-Complex.I) • H) = K + H := by
      rw [smul_smul]
      norm_num [Complex.I_mul_I]
    _ = H + K := add_comm _ _
    _ = Z.1 := StarModule.selfAdjointPart_add_skewAdjointPart ℝ Z.1

/-- The compact real form complex-linearly spans the full special-linear Lie
algebra. -/
theorem complex_span_range_toSpecialLinear_eq_top :
    Submodule.span ℂ
      (Set.range (toSpecialLinear :
        CompactRealForm n → LieAlgebra.SpecialLinear.sl n ℂ)) = ⊤ := by
  apply top_unique
  intro Z _hZ
  rw [← skewPart_add_I_smul_selfPart Z]
  apply Submodule.add_mem
  · exact Submodule.subset_span (Set.mem_range_self (skewPart Z))
  · exact Submodule.smul_mem _ Complex.I
      (Submodule.subset_span (Set.mem_range_self (selfPart Z)))

/-- A complex-linear map out of `sl(n,C)` is uniquely determined on compact
directions. -/
theorem linearMap_ext
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {f g : LieAlgebra.SpecialLinear.sl n ℂ →ₗ[ℂ] W}
    (h : ∀ X : CompactRealForm n,
      f X.toSpecialLinear = g X.toSpecialLinear) :
    f = g := by
  apply LinearMap.ext_on_range complex_span_range_toSpecialLinear_eq_top
  exact h

theorem skewPart_add (Z W : LieAlgebra.SpecialLinear.sl n ℂ) :
    skewPart (Z + W) = skewPart Z + skewPart W := by
  apply ext
  apply Subtype.ext
  simp [skewPart, skewAdjointPart_apply_coe]

theorem selfPart_add (Z W : LieAlgebra.SpecialLinear.sl n ℂ) :
    selfPart (Z + W) = selfPart Z + selfPart W := by
  apply ext
  apply Subtype.ext
  simp [selfPart, selfAdjointPart_apply_coe, add_add_add_comm, smul_add]

theorem skewPart_real_smul (t : ℝ)
    (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    skewPart ((t : ℂ) • Z) = t • skewPart Z := by
  apply ext
  apply Subtype.ext
  simp [skewPart, skewAdjointPart_apply_coe]

theorem selfPart_real_smul (t : ℝ)
    (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    selfPart ((t : ℂ) • Z) = t • selfPart Z := by
  apply ext
  apply Subtype.ext
  simp [selfPart, selfAdjointPart_apply_coe, smul_smul]
  ext i j
  simp
  ring

theorem skewPart_I_smul (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    skewPart (Complex.I • Z) = -selfPart Z := by
  apply ext
  apply Subtype.ext
  ext i j
  simp [skewPart, selfPart, skewAdjointPart_apply_coe,
    selfAdjointPart_apply_coe]
  ring

theorem selfPart_I_smul (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    selfPart (Complex.I • Z) = skewPart Z := by
  apply ext
  apply Subtype.ext
  ext i j
  simp [skewPart, selfPart, skewAdjointPart_apply_coe,
    selfAdjointPart_apply_coe]
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

theorem skewPart_smul (c : ℂ)
    (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    skewPart (c • Z) =
      c.re • skewPart Z - c.im • selfPart Z := by
  rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, skewPart_add, skewPart_real_smul,
    skewPart_real_smul, skewPart_I_smul]
  simp [sub_eq_add_neg]

theorem selfPart_smul (c : ℂ)
    (Z : LieAlgebra.SpecialLinear.sl n ℂ) :
    selfPart (c • Z) =
      c.im • skewPart Z + c.re • selfPart Z := by
  rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, selfPart_add, selfPart_real_smul,
    selfPart_real_smul, selfPart_I_smul]
  simp
  rw [add_comm]

/-- Extend a real-linear map on `su(n)` to a complex-linear map on
`sl(n,C)` using the explicit compact-real-form decomposition. -/
def complexifyRealLinearMap
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : CompactRealForm n →ₗ[ℝ] W) :
    LieAlgebra.SpecialLinear.sl n ℂ →ₗ[ℂ] W where
  toFun Z := D (skewPart Z) + Complex.I • D (selfPart Z)
  map_add' Z W := by
    rw [skewPart_add, selfPart_add, map_add, map_add]
    module
  map_smul' c Z := by
    rw [skewPart_smul, selfPart_smul, map_sub, map_add,
      map_smul, map_smul, map_smul, map_smul]
    apply Eq.symm
    conv_lhs => rw [← Complex.re_add_im c]
    have hc : (c.re : ℂ) + (c.im : ℂ) * Complex.I =
        (c.re : ℂ) + Complex.I * (c.im : ℂ) := by ring
    rw [hc]
    match_scalars
    · simp
    · simp only [id_eq]
      ring_nf
      simp only [pow_two, Complex.I_mul_I]
      rw [mul_comm (c.re : ℂ) Complex.I]
      rw [sub_eq_add_neg]
      rw [neg_one_mul]
      rfl

theorem skewPart_toSpecialLinear (X : CompactRealForm n) :
    skewPart X.toSpecialLinear = X := by
  apply ext
  apply Subtype.ext
  have hX := X.skewAdjoint
  rw [_root_.skewAdjoint.mem_iff] at hX
  simp only [skewPart, skewAdjointPart_apply_coe, hX]
  rw [sub_neg_eq_add, smul_add]
  exact invOf_two_smul_add_invOf_two_smul ℝ
    (X.toSpecialLinear.1 : Matrix n n ℂ)

theorem selfPart_toSpecialLinear (X : CompactRealForm n) :
    selfPart X.toSpecialLinear = 0 := by
  apply ext
  apply Subtype.ext
  have hX := X.skewAdjoint
  rw [_root_.skewAdjoint.mem_iff] at hX
  simp [selfPart, selfAdjointPart_apply_coe, hX]

@[simp]
theorem complexifyRealLinearMap_compact
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : CompactRealForm n →ₗ[ℝ] W) (X : CompactRealForm n) :
    complexifyRealLinearMap D X.toSpecialLinear = D X := by
  simp [complexifyRealLinearMap, skewPart_toSpecialLinear,
    selfPart_toSpecialLinear]

private def underlyingRealLinearMap
    {W : Type*} [LieRing W] [LieAlgebra ℂ W]
    (D : CompactRealForm n →ₗ⁅ℝ⁆ RestrictScalars ℝ ℂ W) :
    CompactRealForm n →ₗ[ℝ] W where
  toFun X := D X
  map_add' X Y := D.map_add X Y
  map_smul' t X := D.map_smul t X

private def mappedBracket
    {L W : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing W] [LieAlgebra ℂ W] (F : L →ₗ[ℂ] W) :
    L →ₗ[ℂ] (L →ₗ[ℂ] W) where
  toFun X :=
    { toFun := fun Y => F ⁅X, Y⁆
      map_add' := by intro Y Z; rw [lie_add, map_add]
      map_smul' := by
        intro c Y
        rw [lie_smul, map_smul]
        simp }
  map_add' X Y := by
    ext Z
    change F ⁅X + Y, Z⁆ = F ⁅X, Z⁆ + F ⁅Y, Z⁆
    rw [add_lie, map_add]
  map_smul' c X := by
    ext Z
    change F ⁅c • X, Z⁆ = c • F ⁅X, Z⁆
    rw [smul_lie, map_smul]

private def bracketOfMapped
    {L W : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing W] [LieAlgebra ℂ W] (F : L →ₗ[ℂ] W) :
    L →ₗ[ℂ] (L →ₗ[ℂ] W) where
  toFun X :=
    { toFun := fun Y => ⁅F X, F Y⁆
      map_add' := by intro Y Z; rw [map_add, lie_add]
      map_smul' := by
        intro c Y
        rw [map_smul, lie_smul]
        simp }
  map_add' X Y := by
    ext Z
    change ⁅F (X + Y), F Z⁆ = ⁅F X, F Z⁆ + ⁅F Y, F Z⁆
    rw [map_add, add_lie]
  map_smul' c X := by
    ext Z
    change ⁅F (c • X), F Z⁆ = c • ⁅F X, F Z⁆
    rw [map_smul, smul_lie]

/-- Every real Lie-algebra homomorphism out of `su(n)` has an explicit
complex Lie-algebra extension to `sl(n,C)`. -/
def complexifyRealLieHom
    {W : Type*} [LieRing W] [LieAlgebra ℂ W]
    (D : CompactRealForm n →ₗ⁅ℝ⁆ RestrictScalars ℝ ℂ W) :
    LieAlgebra.SpecialLinear.sl n ℂ →ₗ⁅ℂ⁆ W where
  toLinearMap := complexifyRealLinearMap (underlyingRealLinearMap D)
  map_lie' := by
    intro Z T
    let F := complexifyRealLinearMap (underlyingRealLinearMap D)
    have h : mappedBracket F = bracketOfMapped F := by
      apply linearMap_ext
      intro X
      apply linearMap_ext
      intro Y
      change F ⁅X.toSpecialLinear, Y.toSpecialLinear⁆ =
        ⁅F X.toSpecialLinear, F Y.toSpecialLinear⁆
      rw [← toSpecialLinear_lie]
      simp only [F, complexifyRealLinearMap_compact]
      exact D.map_lie X Y
    exact LinearMap.congr_fun (LinearMap.congr_fun h Z) T

@[simp]
theorem complexifyRealLieHom_compact
    {W : Type*} [LieRing W] [LieAlgebra ℂ W]
    (D : CompactRealForm n →ₗ⁅ℝ⁆ RestrictScalars ℝ ℂ W)
    (X : CompactRealForm n) :
    complexifyRealLieHom D X.toSpecialLinear = D X := by
  exact complexifyRealLinearMap_compact (underlyingRealLinearMap D) X

/-- The complex Lie-hom extension is uniquely determined by its restriction
to the compact real form. -/
theorem complexifyRealLieHom_unique
    {W : Type*} [LieRing W] [LieAlgebra ℂ W]
    (D : CompactRealForm n →ₗ⁅ℝ⁆ RestrictScalars ℝ ℂ W)
    (F : LieAlgebra.SpecialLinear.sl n ℂ →ₗ⁅ℂ⁆ W)
    (hF : ∀ X : CompactRealForm n, F X.toSpecialLinear = D X) :
    F = complexifyRealLieHom D := by
  apply LieHom.ext
  intro Z
  have hLinear : F.toLinearMap = (complexifyRealLieHom D).toLinearMap := by
    apply linearMap_ext
    intro X
    change F X.toSpecialLinear =
      complexifyRealLieHom D X.toSpecialLinear
    rw [hF X, complexifyRealLieHom_compact]
  exact LinearMap.congr_fun hLinear Z

/-- The ordinary matrix exponential of a compact-real-form element, packaged
as a member of the special unitary group. -/
def expSpecialUnitary (X : CompactRealForm n) :
    Matrix.specialUnitaryGroup n ℂ :=
  letI : NormedAlgebra ℚ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
  letI : IsScalarTower ℚ ℂ (Matrix n n ℂ) :=
    IsScalarTower.restrictScalars ℚ ℂ (Matrix n n ℂ)
  ⟨exp (X : Matrix n n ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · exact exp_mem_unitary_of_mem_skewAdjoint X.skewAdjoint
    · rw [MatrixDeterminantExponential.det_exp]
      have hTrace : Matrix.trace (X : Matrix n n ℂ) = 0 :=
        X.toSpecialLinear.2
      rw [hTrace]
      exact Complex.exp_zero⟩

@[simp]
theorem coe_expSpecialUnitary (X : CompactRealForm n) :
    ((expSpecialUnitary X : Matrix.specialUnitaryGroup n ℂ) :
        Matrix n n ℂ) = exp (X : Matrix n n ℂ) :=
  rfl

@[simp]
theorem expSpecialUnitary_zero :
    expSpecialUnitary (0 : CompactRealForm n) = 1 := by
  apply Subtype.ext
  change exp (0 : Matrix n n ℂ) = 1
  simp

/-- Exponentiating a fixed compact Lie element along real time gives a
multiplicative one-parameter subgroup. -/
theorem expSpecialUnitary_real_smul_add
    (X : CompactRealForm n) (s t : ℝ) :
    expSpecialUnitary ((s + t) • X) =
      expSpecialUnitary (s • X) * expSpecialUnitary (t • X) := by
  apply Subtype.ext
  change exp (((s + t : ℝ) : ℂ) • (X : Matrix n n ℂ)) =
    exp ((s : ℂ) • (X : Matrix n n ℂ)) *
      exp ((t : ℂ) • (X : Matrix n n ℂ))
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _
    ((Commute.refl (X : Matrix n n ℂ)).smul_left _ |>.smul_right _)

/-- Negating time gives the inverse compact one-parameter subgroup. -/
theorem expSpecialUnitary_neg_real_smul
    (X : CompactRealForm n) (t : ℝ) :
    expSpecialUnitary ((-t) • X) =
      (expSpecialUnitary (t • X))⁻¹ := by
  have h := expSpecialUnitary_real_smul_add X t (-t)
  rw [add_neg_cancel, zero_smul, expSpecialUnitary_zero] at h
  calc
    expSpecialUnitary ((-t) • X) =
        1 * expSpecialUnitary ((-t) • X) := by rw [one_mul]
    _ = ((expSpecialUnitary (t • X))⁻¹ *
          expSpecialUnitary (t • X)) *
        expSpecialUnitary ((-t) • X) := by
          rw [inv_mul_cancel]
    _ = (expSpecialUnitary (t • X))⁻¹ * 1 := by
          rw [mul_assoc, ← h]
    _ = (expSpecialUnitary (t • X))⁻¹ := by rw [mul_one]

/-- Negating the generator gives the inverse compact one-parameter
subgroup. -/
theorem expSpecialUnitary_real_smul_neg
    (X : CompactRealForm n) (t : ℝ) :
    expSpecialUnitary (t • (-X)) =
      (expSpecialUnitary (t • X))⁻¹ := by
  rw [← expSpecialUnitary_neg_real_smul X t]
  congr 1
  simp

/-- The underlying invertible matrix of a special unitary element. -/
def matrixUnit (g : Matrix.specialUnitaryGroup n ℂ) :
    (Matrix n n ℂ)ˣ where
  val := g
  inv := ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ)
  val_inv := by
    simpa only [Submonoid.coe_mul, Submonoid.coe_one] using
      congrArg Subtype.val (mul_inv_cancel g)
  inv_val := by
    simpa only [Submonoid.coe_mul, Submonoid.coe_one] using
      congrArg Subtype.val (inv_mul_cancel g)

@[simp]
theorem coe_matrixUnit (g : Matrix.specialUnitaryGroup n ℂ) :
    (matrixUnit g : Matrix n n ℂ) = g := rfl

@[simp]
theorem coe_matrixUnit_inv (g : Matrix.specialUnitaryGroup n ℂ) :
    (((matrixUnit g)⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) =
      ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ) := rfl

/-- Matrix conjugation intertwines the compact exponential with group
conjugation. -/
theorem expSpecialUnitary_smul_conjugate
    (g : Matrix.specialUnitaryGroup n ℂ)
    (Y : CompactRealForm n) (s : ℝ) :
    expSpecialUnitary (s • conjugate g Y) =
      g * expSpecialUnitary (s • Y) * g⁻¹ := by
  apply Subtype.ext
  change
    exp ((s : ℂ) •
      ((g : Matrix n n ℂ) * (Y : Matrix n n ℂ) *
        ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ))) =
      (g : Matrix n n ℂ) * exp ((s : ℂ) • (Y : Matrix n n ℂ)) *
        ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ)
  have hScalar :
      (s : ℂ) •
          ((g : Matrix n n ℂ) * (Y : Matrix n n ℂ) *
            ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ)) =
        (g : Matrix n n ℂ) * ((s : ℂ) • (Y : Matrix n n ℂ)) *
          ((g⁻¹ : Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ) := by
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [hScalar]
  simpa only [coe_matrixUnit, coe_matrixUnit_inv] using
    Matrix.exp_units_conj (matrixUnit g) ((s : ℂ) • (Y : Matrix n n ℂ))

private theorem matrix_exp_conjugate_tendsto
    (X Y : Matrix n n ℂ) :
    Filter.Tendsto
      (fun t : ℝ =>
        ‖t - 0‖⁻¹ *
          ‖(exp (t • X) * Y * exp (t • (-X))) -
              (exp ((0 : ℝ) • X) * Y * exp ((0 : ℝ) • (-X))) -
            (t - 0) • (X * Y - Y * X)‖)
      (nhds 0) (nhds 0) := by
  have hPos : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const X (0 : ℝ)
  have hNeg : HasDerivAt (fun t : ℝ => exp (t • (-X))) (-X) 0 := by
    simpa using hasDerivAt_exp_smul_const (-X) (0 : ℝ)
  have hProduct := (hPos.mul_const Y).mul hNeg
  have hTendsto := hasDerivAt_iff_tendsto.mp hProduct
  simpa [sub_eq_add_neg] using hTendsto

/-- The derivative at zero of the compact adjoint curve is the matrix
commutator. -/
theorem conjugate_exp_hasDerivAt
    (X Y : CompactRealForm n) :
    HasDerivAt
      (fun t : ℝ => conjugate (expSpecialUnitary (t • X)) Y)
      ⁅X, Y⁆ 0 := by
  rw [hasDerivAt_iff_tendsto]
  have hMatrix := matrix_exp_conjugate_tendsto
    (X : Matrix n n ℂ) (Y : Matrix n n ℂ)
  have hInv (s : ℝ) :
      (((expSpecialUnitary (s • X))⁻¹ :
          Matrix.specialUnitaryGroup n ℂ) : Matrix n n ℂ) =
        exp (s • (-(X : Matrix n n ℂ))) := by
    rw [← expSpecialUnitary_neg_real_smul X s]
    simp
  convert hMatrix using 1
  funext t
  apply congrArg (fun z : ℝ => ‖t - 0‖⁻¹ * z)
  change
    ‖toMatrixRealLinear
      (conjugate (expSpecialUnitary (t • X)) Y -
        conjugate (expSpecialUnitary ((0 : ℝ) • X)) Y -
        (t - 0) • ⁅X, Y⁆)‖ = _
  rw [map_sub, map_sub, map_smul]
  change
    ‖((conjugate (expSpecialUnitary (t • X)) Y :
          CompactRealForm n) : Matrix n n ℂ) -
        ((conjugate (expSpecialUnitary ((0 : ℝ) • X)) Y :
          CompactRealForm n) : Matrix n n ℂ) -
        (t - 0) • ((⁅X, Y⁆ : CompactRealForm n) : Matrix n n ℂ)‖ = _
  rw [coe_conjugate, coe_conjugate, hInv t, hInv 0]
  rfl

@[simp]
theorem expSpecialUnitary_zero_smul (X : CompactRealForm n) :
    expSpecialUnitary ((0 : ℝ) • X) = 1 := by
  apply Subtype.ext
  change exp (((0 : ℝ) : ℂ) • (X : Matrix n n ℂ)) = 1
  simp

/-- Surjectivity of the compact exponential immediately supplies the
finite-product generation package consumed by the semisimple embedding classification integration bridge. -/
def finiteProductGenerationOfSurjective
    (hExp : Function.Surjective (expSpecialUnitary (n := n))) :
    FiniteProductGeneration (Matrix.specialUnitaryGroup n ℂ)
      (CompactRealForm n) :=
  FiniteProductGeneration.ofSurjective expSpecialUnitary hExp

end CompactRealForm

end General

/-!
## The distinguished `SU(2)` center parameter
-/

/-- `pi * I * H`, now regarded as an element of the compact real form
`su(2)`. -/
def su2CenterParameter : CompactRealForm (Fin 2) where
  toSpecialLinear := su2CenterLieElement
  skewAdjoint := by
    rw [skewAdjoint.mem_iff]
    rw [SpecialUnitaryExponential.su2CenterLieElement_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp

@[simp]
theorem su2CenterParameter_toSpecialLinear :
    su2CenterParameter.toSpecialLinear = su2CenterLieElement :=
  rfl

/-- The compact exponential sends the distinguished Lie element to the
nontrivial center of `SU(2)`. -/
theorem expSpecialUnitary_su2CenterParameter :
    CompactRealForm.expSpecialUnitary su2CenterParameter = su2CenterElement := by
  apply Subtype.ext
  exact SpecialUnitaryExponential.exp_su2CenterLieElement

/-!
## Ready-to-use semisimple embedding classification model constructors
-/

universe v

/-- Once a differentiated `SU(2)` action is compatible with the concrete
compact exponential and that exponential is surjective, all fields of the
sharper generated-exponential semisimple embedding classification model are constructed. -/
def su2GeneratedModelOfSurjectiveExponential
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V)
    [FiniteDimensional ℂ V]
    [LieRingModule StandardSl2.Algebra V]
    [LieModule ℂ StandardSl2.Algebra V]
    (hExp : Function.Surjective
      (CompactRealForm.expSpecialUnitary (n := Fin 2)))
    (hAction : ∀ X : CompactRealForm (Fin 2),
      rho (CompactRealForm.expSpecialUnitary X) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl2.Algebra V X.toSpecialLinear)) :
    SU2GeneratedExponentialStandardLieModel rho where
  finiteDimensional := inferInstance
  lieRingModule := inferInstance
  lieModule := inferInstance
  parameter := CompactRealForm (Fin 2)
  generation := CompactRealForm.finiteProductGenerationOfSurjective hExp
  toComplexLie := CompactRealForm.toSpecialLinear
  action_generator := hAction
  centerParameter := su2CenterParameter
  center_generator := expSpecialUnitary_su2CenterParameter
  center_lie := rfl

/-- The analogous constructor for a differentiated `SU(3)` action. -/
def su3ModelOfSurjectiveExponential
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V)
    [FiniteDimensional ℂ V]
    [LieRingModule StandardSl3.Algebra V]
    [LieModule ℂ StandardSl3.Algebra V]
    (hExp : Function.Surjective
      (CompactRealForm.expSpecialUnitary (n := Fin 3)))
    (hAction : ∀ X : CompactRealForm (Fin 3),
      rho (CompactRealForm.expSpecialUnitary X) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl3.Algebra V X.toSpecialLinear)) :
    SU3ExponentiallyIntegratedStandardLieModel rho where
  finiteDimensional := inferInstance
  lieRingModule := inferInstance
  lieModule := inferInstance
  parameter := CompactRealForm (Fin 3)
  generation := CompactRealForm.finiteProductGenerationOfSurjective hExp
  toComplexLie := CompactRealForm.toSpecialLinear
  action_generator := hAction

/-!
## Differentiated-action certificates

These structures isolate the representation-dependent analytic input from
the group-dependent surjectivity of the compact exponential.  They contain
exactly a differentiated standard Lie action and the compatibility equation
needed by the already checked finite-product integration argument.
-/

/-- A differentiated `SU(2)` representation compatible with the concrete
compact-real-form exponential. -/
structure SU2DifferentiatedExponentialAction
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V) where
  [finiteDimensional : FiniteDimensional ℂ V]
  [lieRingModule : LieRingModule StandardSl2.Algebra V]
  [lieModule : LieModule ℂ StandardSl2.Algebra V]
  action_exp : ∀ X : CompactRealForm (Fin 2),
    rho (CompactRealForm.expSpecialUnitary X) =
      finiteDimensionalExponential
        (LieModule.toEnd ℂ StandardSl2.Algebra V X.toSpecialLinear)

namespace SU2DifferentiatedExponentialAction

/-- Surjectivity of the concrete compact exponential upgrades a compatible
differentiated action to the generated model consumed by semisimple embedding classification. -/
def toGeneratedModel
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    (D : SU2DifferentiatedExponentialAction rho)
    (hExp : Function.Surjective
      (CompactRealForm.expSpecialUnitary (n := Fin 2))) :
    SU2GeneratedExponentialStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := D.finiteDimensional
  letI : LieRingModule StandardSl2.Algebra V := D.lieRingModule
  letI : LieModule ℂ StandardSl2.Algebra V := D.lieModule
  exact su2GeneratedModelOfSurjectiveExponential rho hExp D.action_exp

end SU2DifferentiatedExponentialAction

/-- A differentiated `SU(3)` representation compatible with the concrete
compact-real-form exponential. -/
structure SU3DifferentiatedExponentialAction
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) where
  [finiteDimensional : FiniteDimensional ℂ V]
  [lieRingModule : LieRingModule StandardSl3.Algebra V]
  [lieModule : LieModule ℂ StandardSl3.Algebra V]
  action_exp : ∀ X : CompactRealForm (Fin 3),
    rho (CompactRealForm.expSpecialUnitary X) =
      finiteDimensionalExponential
        (LieModule.toEnd ℂ StandardSl3.Algebra V X.toSpecialLinear)

namespace SU3DifferentiatedExponentialAction

/-- Surjectivity of the concrete compact exponential upgrades a compatible
differentiated action to the exponential model consumed by semisimple embedding classification. -/
def toExponentialModel
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU3 V}
    (D : SU3DifferentiatedExponentialAction rho)
    (hExp : Function.Surjective
      (CompactRealForm.expSpecialUnitary (n := Fin 3))) :
    SU3ExponentiallyIntegratedStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := D.finiteDimensional
  letI : LieRingModule StandardSl3.Algebra V := D.lieRingModule
  letI : LieModule ℂ StandardSl3.Algebra V := D.lieModule
  exact su3ModelOfSurjectiveExponential rho hExp D.action_exp

end SU3DifferentiatedExponentialAction

end

end SpecialUnitaryLieAlgebra
end GUT
