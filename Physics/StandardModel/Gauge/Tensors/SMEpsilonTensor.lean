import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Epsilon contractions as linear maps on tensor products

The two- and three-dimensional determinant tensors are evaluated on rows.
Their invariance uses the full determinant-one matrix action, not weights.
-/

set_option autoImplicit false

namespace Physics.SMEpsilonTensor

noncomputable section

open scoped TensorProduct

abbrev Color := Fin 3 → ℂ
abbrev Weak := Fin 2 → ℂ

def eps2 (a b : Weak) : ℂ := a 0 * b 1 - a 1 * b 0

def eps3 (a b c : Color) : ℂ :=
  a 0 * b 1 * c 2 + a 1 * b 2 * c 0 + a 2 * b 0 * c 1 -
    a 2 * b 1 * c 0 - a 1 * b 0 * c 2 - a 0 * b 2 * c 1

def eps2Bilin : Weak →ₗ[ℂ] Weak →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ eps2
    (by intros; simp [eps2, add_mul]; ring)
    (by intros; simp [eps2]; ring)
    (by intros; simp [eps2, mul_add]; ring)
    (by intros; simp [eps2]; ring)

private def eps3Last (a b : Color) : Color →ₗ[ℂ] ℂ where
  toFun := eps3 a b
  map_add' := by intros; simp [eps3, mul_add]; ring
  map_smul' := by intros; simp [eps3]; ring

def eps3Trilin : Color →ₗ[ℂ] Color →ₗ[ℂ] Color →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ eps3Last
    (by intros; ext; simp [eps3Last, eps3, add_mul]; ring)
    (by intros; ext; simp [eps3Last, eps3]; ring)
    (by intros; ext; simp [eps3Last, eps3, mul_add, add_mul]; ring)
    (by intros; ext; simp [eps3Last, eps3]; ring)

@[simp] theorem eps2_smul_left (r : ℂ) (a b : Weak) :
    eps2 (r • a) b = r * eps2 a b := by simp [eps2]; ring

@[simp] theorem eps2_smul_right (r : ℂ) (a b : Weak) :
    eps2 a (r • b) = r * eps2 a b := by simp [eps2]; ring

@[simp] theorem eps3_smul_first (r : ℂ) (a b c : Color) :
    eps3 (r • a) b c = r * eps3 a b c := by simp [eps3]; ring

@[simp] theorem eps3_smul_second (r : ℂ) (a b c : Color) :
    eps3 a (r • b) c = r * eps3 a b c := by simp [eps3]; ring

@[simp] theorem eps3_smul_third (r : ℂ) (a b c : Color) :
    eps3 a b (r • c) = r * eps3 a b c := by simp [eps3]; ring

def weakTensor : Weak ⊗[ℂ] Weak →ₗ[ℂ] ℂ := TensorProduct.lift eps2Bilin

def colorTensor : (Color ⊗[ℂ] Color) ⊗[ℂ] Color →ₗ[ℂ] ℂ :=
  TensorProduct.lift (TensorProduct.lift eps3Trilin)

@[simp] theorem weakTensor_tmul (a b : Weak) : weakTensor (a ⊗ₜ[ℂ] b) = eps2 a b := rfl

@[simp] theorem colorTensor_tmul (a b c : Color) :
    colorTensor ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) = eps3 a b c := rfl

theorem eps2_det (a b : Weak) : eps2 a b = Matrix.det (Matrix.of ![a, b]) := by
  rw [Matrix.det_fin_two]
  rfl

theorem eps3_det (a b c : Color) : eps3 a b c = Matrix.det (Matrix.of ![a, b, c]) := by
  rw [Matrix.det_fin_three]
  simp [eps3]
  ring

private theorem det_rows_mulVec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : Matrix.det g = 1) (v : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.det (Matrix.of fun i => g.mulVec (v i)) = Matrix.det v := by
  have he : (Matrix.of fun i => g.mulVec (v i)) = v * g.transpose := by
    ext i j
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  rw [he, Matrix.det_mul, Matrix.det_transpose, hg, mul_one]

theorem eps2_invariant (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : Matrix.det g = 1)
    (a b : Weak) : eps2 (g.mulVec a) (g.mulVec b) = eps2 a b := by
  rw [eps2_det, eps2_det]
  convert det_rows_mulVec g hg (Matrix.of ![a, b]) using 1
  congr 1
  ext i j
  fin_cases i <;> rfl

theorem eps3_invariant (g : Matrix (Fin 3) (Fin 3) ℂ) (hg : Matrix.det g = 1)
    (a b c : Color) : eps3 (g.mulVec a) (g.mulVec b) (g.mulVec c) = eps3 a b c := by
  rw [eps3_det, eps3_det]
  convert det_rows_mulVec g hg (Matrix.of ![a, b, c]) using 1
  congr 1
  ext i j
  fin_cases i <;> rfl

def colorBasis (i : Fin 3) : Color := Pi.single i 1
def weakBasis (i : Fin 2) : Weak := Pi.single i 1

@[simp] theorem eps3_basis : eps3 (colorBasis 0) (colorBasis 1) (colorBasis 2) = 1 := by
  simp [eps3, colorBasis]

@[simp] theorem eps2_basis : eps2 (weakBasis 0) (weakBasis 1) = 1 := by
  simp [eps2, weakBasis]

end

end Physics.SMEpsilonTensor
