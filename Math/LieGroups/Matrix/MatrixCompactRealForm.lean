import TauCeti.LinearAlgebra.Complex.Conjugation
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The skew-Hermitian real form of an adjoint-stable matrix Lie algebra

The complexification is an isomorphism of Lie algebras, not just vector spaces.
No subgroup or Lie-group integration is constructed here.
-/

set_option autoImplicit false

namespace Math.MatrixCompactRealForm

open scoped Matrix TensorProduct

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem adjoint_lie (x y : Matrix n n ℂ) : (⁅x, y⁆)ᴴ = ⁅yᴴ, xᴴ⁆ := by
  simp only [Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]

/-- Paired adjoints on generators extend to the entire complex Lie span. -/
theorem adjoint_mem_lieSpan {ι : Type*} (E F : ι → Matrix n n ℂ)
    (hEF : ∀ i, (E i)ᴴ = F i) (x : Matrix n n ℂ)
    (hx : x ∈ LieSubalgebra.lieSpan ℂ (Matrix n n ℂ) (Set.range E ∪ Set.range F)) :
    xᴴ ∈ LieSubalgebra.lieSpan ℂ (Matrix n n ℂ) (Set.range E ∪ Set.range F) := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [hEF]
      exact LieSubalgebra.subset_lieSpan (Or.inr ⟨i, rfl⟩)
    · rw [← hEF, Matrix.conjTranspose_conjTranspose]
      exact LieSubalgebra.subset_lieSpan (Or.inl ⟨i, rfl⟩)
  | zero => simpa only [Matrix.conjTranspose_zero] using LieSubalgebra.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [Matrix.conjTranspose_add]
    exact LieSubalgebra.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [Matrix.conjTranspose_smul]
    exact LieSubalgebra.smul_mem _ _ ih
  | lie x y hx hy ihx ihy =>
    rw [adjoint_lie]
    exact LieSubalgebra.lie_mem _ ihy ihx

variable (L : LieSubalgebra ℂ (Matrix n n ℂ))

instance realLieAlgebra : LieAlgebra ℝ L where
  lie_smul t x y := Subtype.ext (lie_smul t (x : Matrix n n ℂ) (y : Matrix n n ℂ))

variable (hL : ∀ x ∈ L, xᴴ ∈ L)

/-- Compact conjugation on the complex matrix algebra. -/
def conjugation : L →ₛₗ[starRingEnd ℂ] L where
  toFun x := ⟨-(x : Matrix n n ℂ)ᴴ, L.neg_mem (hL x x.property)⟩
  map_add' x y := by ext i j; simp [Matrix.conjTranspose_add, add_comm]
  map_smul' c x := by ext i j; simp [Matrix.conjTranspose_smul]

@[simp] theorem conjugation_val (x : L) :
    (conjugation L hL x : Matrix n n ℂ) = -(x : Matrix n n ℂ)ᴴ := rfl

theorem conjugation_involutive : Function.Involutive (conjugation L hL) := by
  intro x
  apply Subtype.ext
  simp

theorem conjugation_lie (x y : L) :
    conjugation L hL ⁅x, y⁆ = ⁅conjugation L hL x, conjugation L hL y⁆ := by
  apply Subtype.ext
  change -(⁅(x : Matrix n n ℂ), (y : Matrix n n ℂ)⁆)ᴴ = ⁅-_, -_⁆
  rw [adjoint_lie, neg_lie, lie_neg, neg_neg, lie_skew]

/-- The fixed Lie algebra of compact conjugation, over the real numbers. -/
def realForm : LieSubalgebra ℝ L where
  toSubmodule := TauCeti.realPoints (conjugation L hL)
  lie_mem' {x y} hx hy := by
    change conjugation L hL ⁅x, y⁆ = ⁅x, y⁆
    rw [conjugation_lie, (TauCeti.mem_realPoints.mp hx), (TauCeti.mem_realPoints.mp hy)]

theorem mem_realForm (x : L) :
    x ∈ realForm L hL ↔ (x : Matrix n n ℂ)ᴴ = -(x : Matrix n n ℂ) := by
  change conjugation L hL x = x ↔ _
  constructor
  · intro h
    have hv := congrArg (fun z : L => (z : Matrix n n ℂ)) h
    change -(x : Matrix n n ℂ)ᴴ = (x : Matrix n n ℂ) at hv
    exact neg_eq_iff_eq_neg.mp hv
  · intro h
    apply Subtype.ext
    change -(x : Matrix n n ℂ)ᴴ = (x : Matrix n n ℂ)
    rw [h, neg_neg]

/-- The underlying vector-space comparison supplied by conjugation. -/
def complexificationLinear : ℂ ⊗[ℝ] realForm L hL ≃ₗ[ℂ] L :=
  TauCeti.realPointsEquiv (conjugation_involutive L hL)

@[simp] theorem complexificationLinear_tmul (c : ℂ) (x : realForm L hL) :
    complexificationLinear L hL (c ⊗ₜ[ℝ] x) = c • (x : L) :=
  TauCeti.realPointsEquiv_tmul (conjugation_involutive L hL) c x

set_option backward.isDefEq.respectTransparency false in
/-- Canonical complexification of the fixed Lie algebra. -/
def complexification : ℂ ⊗[ℝ] realForm L hL ≃ₗ⁅ℂ⁆ L where
  __ := complexificationLinear L hL
  map_lie' {x y} := by
    change complexificationLinear L hL ⁅x, y⁆ =
      ⁅complexificationLinear L hL x, complexificationLinear L hL y⁆
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_lie, map_add, hx, hy]
    | tmul c x =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz =>
        rw [lie_add (c ⊗ₜ[ℝ] x) y z, map_add, hy, hz, map_add, lie_add]
      | tmul d y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, complexificationLinear_tmul,
          smul_lie, lie_smul, smul_smul]
        rw [mul_comm c d]
        rfl

@[simp] theorem complexification_tmul (c : ℂ) (x : realForm L hL) :
    complexification L hL (c ⊗ₜ[ℝ] x) = c • (x : L) :=
  complexificationLinear_tmul L hL c x

theorem finrank_realForm :
    Module.finrank ℝ (realForm L hL) = Module.finrank ℂ L :=
  TauCeti.finrank_realPoints (conjugation_involutive L hL)

/-- The real form acts by its actual skew-Hermitian matrices. -/
def representation : realForm L hL →ₗ⁅ℝ⁆ Matrix n n ℂ where
  toFun x := x.val.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

theorem representation_injective : Function.Injective (representation L hL) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem representation_adjoint (x : realForm L hL) :
    (representation L hL x)ᴴ = -representation L hL x :=
  (mem_realForm L hL _).mp x.property

variable (M : LieSubalgebra ℂ (Matrix n n ℂ)) (hM : ∀ x ∈ M, xᴴ ∈ M) (hle : L ≤ M)

/-- Inclusion of adjoint-stable algebras restricts to their real forms. -/
def inclusion : realForm L hL →ₗ⁅ℝ⁆ realForm M hM where
  toFun x := ⟨⟨x.val.val, hle x.val.property⟩,
    (mem_realForm M hM _).mpr ((mem_realForm L hL _).mp x.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

theorem inclusion_injective : Function.Injective (inclusion L hL M hM hle) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : realForm M hM => z.val.val) h

@[simp] theorem inclusion_val (x : realForm L hL) :
    (inclusion L hL M hM hle x).val.val = x.val.val := rfl

end

end Math.MatrixCompactRealForm
