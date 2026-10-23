import Physics.FieldTheory.Spinor.Weyl.WeylSpinor
import Mathlib.Tactic

/-!
# Six right-Weyl invariant tensors

An exact coordinate proof that every invariant six-linear functional on the
right Weyl representation is spanned by five products of epsilon pairings.
The proof uses only one diagonal and one shear element of `SL(2,C)`.
-/

namespace Physics.SixWeylInvariant

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section

open SMEpsilonTensor WeylSpinor

abbrev Spin := WeylSpinor.Space

abbrev Coefficient :=
  Spin →ₗ[ℂ] Spin →ₗ[ℂ] Spin →ₗ[ℂ] Spin →ₗ[ℂ] Spin →ₗ[ℂ] Spin →ₗ[ℂ] ℂ

def IsInvariant (f : Coefficient) : Prop :=
  ∀ g a b c d e x,
    f (right g a) (right g b) (right g c) (right g d) (right g e) (right g x) =
      f a b c d e x

def basisValue (f : Coefficient) (i j k l m n : Fin 2) : ℂ :=
  f (weakBasis i) (weakBasis j) (weakBasis k)
    (weakBasis l) (weakBasis m) (weakBasis n)

/-- Five noncrossing epsilon-pairing coordinate functions. -/
def pairingValue (p : Fin 5) (a b c d e x : Spin) : ℂ := match p with
  | 0 => eps2 a b * eps2 c d * eps2 e x
  | 1 => eps2 a b * eps2 c x * eps2 d e
  | 2 => eps2 a d * eps2 b c * eps2 e x
  | 3 => eps2 a x * eps2 b c * eps2 d e
  | 4 => eps2 a x * eps2 b e * eps2 c d

private def diagonal : WeylSpinor.Group :=
  ⟨!![1 + Complex.I, 0; 0, (1 - Complex.I) / 2], by
    norm_num [Matrix.det_fin_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im]⟩

private def shear : WeylSpinor.Group :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

private def eigenvalue (i : Fin 2) : ℂ := ![1 - Complex.I, (1 + Complex.I) / 2] i

private theorem diagonal_right (i : Fin 2) :
    right diagonal (weakBasis i) = eigenvalue i • weakBasis i := by
  rw [right_apply]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonal, eigenvalue, weakBasis, Matrix.mulVec, map_ofNat] ; ring

private theorem diagonal_constraint (f : Coefficient) (hf : IsInvariant f)
    (i j k l m n : Fin 2) :
    (eigenvalue i * eigenvalue j * eigenvalue k * eigenvalue l * eigenvalue m *
      eigenvalue n - 1) * basisValue f i j k l m n = 0 := by
  have h := hf diagonal (weakBasis i) (weakBasis j) (weakBasis k)
    (weakBasis l) (weakBasis m) (weakBasis n)
  simp only [diagonal_right, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  change eigenvalue n * (eigenvalue m * (eigenvalue l *
    (eigenvalue k * (eigenvalue j * (eigenvalue i * basisValue f i j k l m n))))) =
      basisValue f i j k l m n at h
  linear_combination h

theorem basisValue_vanish (f : Coefficient) (hf : IsInvariant f)
    (i j k l m n : Fin 2)
    (hcount : i.val + j.val + k.val + l.val + m.val + n.val ≠ 3) :
    basisValue f i j k l m n = 0 := by
  have h := diagonal_constraint f hf i j k l m n
  have hn : eigenvalue i * eigenvalue j * eigenvalue k * eigenvalue l * eigenvalue m *
      eigenvalue n - 1 ≠ 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      fin_cases m <;> fin_cases n
    all_goals norm_num at hcount
    all_goals norm_num [eigenvalue, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  exact (mul_eq_zero.mp h).resolve_left hn

private theorem shear_right_zero : right shear (weakBasis 0) = weakBasis 0 := by
  rw [right_apply]
  ext i
  fin_cases i <;> simp [shear, weakBasis, Matrix.mulVec]

private theorem shear_right_one :
    right shear (weakBasis 1) = weakBasis 0 + weakBasis 1 := by
  rw [right_apply]
  ext i
  fin_cases i <;> simp [shear, weakBasis, Matrix.mulVec]

private theorem shear_constraint (f : Coefficient) (hf : IsInvariant f)
    (i j k l m n : Fin 2) :
    f (right shear (weakBasis i)) (right shear (weakBasis j))
      (right shear (weakBasis k)) (right shear (weakBasis l))
      (right shear (weakBasis m)) (right shear (weakBasis n)) =
        basisValue f i j k l m n :=
  hf shear (weakBasis i) (weakBasis j) (weakBasis k)
    (weakBasis l) (weakBasis m) (weakBasis n)

private theorem basisValue_eq (f : Coefficient) (i j k l m n : Fin 2) :
    f (weakBasis i) (weakBasis j) (weakBasis k)
      (weakBasis l) (weakBasis m) (weakBasis n) = basisValue f i j k l m n := rfl

private theorem raw_vanish (f : Coefficient) (hf : IsInvariant f)
    (i j k l m n : Fin 2)
    (hcount : i.val + j.val + k.val + l.val + m.val + n.val ≠ 3) :
    f (weakBasis i) (weakBasis j) (weakBasis k)
      (weakBasis l) (weakBasis m) (weakBasis n) = 0 :=
  basisValue_vanish f hf i j k l m n hcount

set_option maxHeartbeats 10000000 in
private theorem basisValue_formula (f : Coefficient) (hf : IsInvariant f)
    (i j k l m n : Fin 2) :
    basisValue f i j k l m n =
      (basisValue f 0 1 0 1 0 1 + basisValue f 0 1 0 0 1 1 +
          basisValue f 0 0 1 1 0 1 + basisValue f 0 0 1 0 1 1 +
          2 * basisValue f 0 0 0 1 1 1) *
        pairingValue 0 (weakBasis i) (weakBasis j) (weakBasis k)
          (weakBasis l) (weakBasis m) (weakBasis n) +
      (basisValue f 0 1 0 0 1 1 + basisValue f 0 0 1 0 1 1 +
          basisValue f 0 0 0 1 1 1) *
        pairingValue 1 (weakBasis i) (weakBasis j) (weakBasis k)
          (weakBasis l) (weakBasis m) (weakBasis n) +
      (basisValue f 0 0 1 1 0 1 + basisValue f 0 0 1 0 1 1 +
          basisValue f 0 0 0 1 1 1) *
        pairingValue 2 (weakBasis i) (weakBasis j) (weakBasis k)
          (weakBasis l) (weakBasis m) (weakBasis n) +
      (basisValue f 0 0 1 0 1 1 + basisValue f 0 0 0 1 1 1) *
        pairingValue 3 (weakBasis i) (weakBasis j) (weakBasis k)
          (weakBasis l) (weakBasis m) (weakBasis n) +
      basisValue f 0 0 0 1 1 1 *
        pairingValue 4 (weakBasis i) (weakBasis j) (weakBasis k)
          (weakBasis l) (weakBasis m) (weakBasis n) := by
  have h001111 := shear_constraint f hf 0 0 1 1 1 1
  have h010111 := shear_constraint f hf 0 1 0 1 1 1
  have h011011 := shear_constraint f hf 0 1 1 0 1 1
  have h011101 := shear_constraint f hf 0 1 1 1 0 1
  have h011110 := shear_constraint f hf 0 1 1 1 1 0
  have h100111 := shear_constraint f hf 1 0 0 1 1 1
  have h101011 := shear_constraint f hf 1 0 1 0 1 1
  have h101101 := shear_constraint f hf 1 0 1 1 0 1
  have h101110 := shear_constraint f hf 1 0 1 1 1 0
  have h110011 := shear_constraint f hf 1 1 0 0 1 1
  have h110101 := shear_constraint f hf 1 1 0 1 0 1
  have h110110 := shear_constraint f hf 1 1 0 1 1 0
  have h111001 := shear_constraint f hf 1 1 1 0 0 1
  have h111010 := shear_constraint f hf 1 1 1 0 1 0
  have h111100 := shear_constraint f hf 1 1 1 1 0 0
  simp only [shear_right_zero, shear_right_one, map_add] at h001111 h010111 h011011 h011101 h011110 h100111 h101011 h101101 h101110 h110011 h110101 h110110 h111001 h111010 h111100
  simp [raw_vanish f hf, basisValue_vanish f hf] at h001111 h010111 h011011 h011101 h011110 h100111 h101011 h101101 h101110 h110011 h110101 h110110 h111001 h111010 h111100
  by_cases hc : i.val + j.val + k.val + l.val + m.val + n.val ≠ 3
  · rw [basisValue_vanish f hf i j k l m n hc]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      fin_cases m <;> fin_cases n
    all_goals norm_num at hc
    all_goals simp [pairingValue, eps2, weakBasis]
  · have hc' : i.val + j.val + k.val + l.val + m.val + n.val = 3 :=
      not_ne_iff.mp hc
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      fin_cases m <;> fin_cases n
    all_goals norm_num at hc'
    all_goals simp [pairingValue, eps2, weakBasis]
    all_goals simp only [basisValue] at h001111 h010111 h011011 h011101 h011110 h100111 h101011 h101101 h101110 h110011 h110101 h110110 h111001 h111010 h111100 ⊢
    all_goals try { ring }
    next => linear_combination h001111
    next => linear_combination h010111
    next => linear_combination (-1 / 2 : ℂ) * h011110 + (1 / 2 : ℂ) * h011101 + (1 / 2 : ℂ) * h011011 + (1 / 2 : ℂ) * h010111 + (1 / 2 : ℂ) * h001111
    next => linear_combination (1 / 2 : ℂ) * h011110 + (-1 / 2 : ℂ) * h011101 + (1 / 2 : ℂ) * h011011 + (-1 / 2 : ℂ) * h010111 + (-1 / 2 : ℂ) * h001111
    next => linear_combination (1 / 2 : ℂ) * h011110 + (1 / 2 : ℂ) * h011101 + (-1 / 2 : ℂ) * h011011 + (-1 / 2 : ℂ) * h010111 + (-1 / 2 : ℂ) * h001111
    next => linear_combination (1 / 3 : ℂ) * h111100 + (-1 / 6 : ℂ) * h111010 + (-1 / 6 : ℂ) * h111001 + (-1 / 6 : ℂ) * h110110 + (-1 / 6 : ℂ) * h110101 + (1 / 3 : ℂ) * h110011 + (-1 / 6 : ℂ) * h101110 + (-1 / 6 : ℂ) * h101101 + (1 / 3 : ℂ) * h101011 + (1 / 3 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (1 / 3 : ℂ) * h011011 + (1 / 3 : ℂ) * h010111 + (1 / 3 : ℂ) * h001111
    next => linear_combination (-1 / 6 : ℂ) * h111100 + (1 / 3 : ℂ) * h111010 + (-1 / 6 : ℂ) * h111001 + (-1 / 6 : ℂ) * h110110 + (1 / 3 : ℂ) * h110101 + (-1 / 6 : ℂ) * h110011 + (-1 / 6 : ℂ) * h101110 + (1 / 3 : ℂ) * h101101 + (-1 / 6 : ℂ) * h101011 + (1 / 3 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (1 / 3 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (1 / 3 : ℂ) * h010111 + (1 / 3 : ℂ) * h001111
    next => linear_combination (-1 / 6 : ℂ) * h111100 + (-1 / 6 : ℂ) * h111010 + (1 / 3 : ℂ) * h111001 + (1 / 3 : ℂ) * h110110 + (-1 / 6 : ℂ) * h110101 + (-1 / 6 : ℂ) * h110011 + (1 / 3 : ℂ) * h101110 + (-1 / 6 : ℂ) * h101101 + (-1 / 6 : ℂ) * h101011 + (1 / 3 : ℂ) * h100111 + (1 / 3 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (-2 / 3 : ℂ) * h010111 + (-2 / 3 : ℂ) * h001111
    next => linear_combination (-1 / 6 : ℂ) * h111100 + (-1 / 6 : ℂ) * h111010 + (1 / 3 : ℂ) * h111001 + (1 / 3 : ℂ) * h110110 + (-1 / 6 : ℂ) * h110101 + (-1 / 6 : ℂ) * h110011 + (-1 / 6 : ℂ) * h101110 + (1 / 3 : ℂ) * h101101 + (1 / 3 : ℂ) * h101011 + (-1 / 6 : ℂ) * h100111 + (1 / 3 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (-2 / 3 : ℂ) * h010111 + (-1 / 6 : ℂ) * h001111
    next => linear_combination (-1 / 6 : ℂ) * h111100 + (1 / 3 : ℂ) * h111010 + (-1 / 6 : ℂ) * h111001 + (-1 / 6 : ℂ) * h110110 + (1 / 3 : ℂ) * h110101 + (-1 / 6 : ℂ) * h110011 + (1 / 3 : ℂ) * h101110 + (-1 / 6 : ℂ) * h101101 + (1 / 3 : ℂ) * h101011 + (-1 / 6 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (1 / 3 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (1 / 3 : ℂ) * h010111 + (-1 / 6 : ℂ) * h001111
    next => linear_combination (1 / 3 : ℂ) * h111100 + (-1 / 6 : ℂ) * h111010 + (-1 / 6 : ℂ) * h111001 + (-1 / 6 : ℂ) * h110110 + (-1 / 6 : ℂ) * h110101 + (1 / 3 : ℂ) * h110011 + (1 / 3 : ℂ) * h101110 + (1 / 3 : ℂ) * h101101 + (-1 / 6 : ℂ) * h101011 + (-1 / 6 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (1 / 3 : ℂ) * h011011 + (1 / 3 : ℂ) * h010111 + (-1 / 6 : ℂ) * h001111
    next => linear_combination (-1 / 6 : ℂ) * h111100 + (-1 / 6 : ℂ) * h111010 + (1 / 3 : ℂ) * h111001 + (-1 / 6 : ℂ) * h110110 + (1 / 3 : ℂ) * h110101 + (1 / 3 : ℂ) * h110011 + (1 / 3 : ℂ) * h101110 + (-1 / 6 : ℂ) * h101101 + (-1 / 6 : ℂ) * h101011 + (-1 / 6 : ℂ) * h100111 + (1 / 3 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (-1 / 6 : ℂ) * h010111 + (-2 / 3 : ℂ) * h001111
    next => linear_combination (-1 / 6 : ℂ) * h111100 + (1 / 3 : ℂ) * h111010 + (-1 / 6 : ℂ) * h111001 + (1 / 3 : ℂ) * h110110 + (-1 / 6 : ℂ) * h110101 + (1 / 3 : ℂ) * h110011 + (-1 / 6 : ℂ) * h101110 + (1 / 3 : ℂ) * h101101 + (-1 / 6 : ℂ) * h101011 + (-1 / 6 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (1 / 3 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (-1 / 6 : ℂ) * h010111 + (1 / 3 : ℂ) * h001111
    next => linear_combination (1 / 3 : ℂ) * h111100 + (-1 / 6 : ℂ) * h111010 + (-1 / 6 : ℂ) * h111001 + (1 / 3 : ℂ) * h110110 + (1 / 3 : ℂ) * h110101 + (-1 / 6 : ℂ) * h110011 + (-1 / 6 : ℂ) * h101110 + (-1 / 6 : ℂ) * h101101 + (1 / 3 : ℂ) * h101011 + (-1 / 6 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (1 / 3 : ℂ) * h011011 + (-1 / 6 : ℂ) * h010111 + (1 / 3 : ℂ) * h001111
    next => linear_combination (1 / 3 : ℂ) * h111100 + (1 / 3 : ℂ) * h111010 + (1 / 3 : ℂ) * h111001 + (-1 / 6 : ℂ) * h110110 + (-1 / 6 : ℂ) * h110101 + (-1 / 6 : ℂ) * h110011 + (-1 / 6 : ℂ) * h101110 + (-1 / 6 : ℂ) * h101101 + (-1 / 6 : ℂ) * h101011 + (1 / 3 : ℂ) * h100111 + (-1 / 6 : ℂ) * h011110 + (-1 / 6 : ℂ) * h011101 + (-1 / 6 : ℂ) * h011011 + (1 / 3 : ℂ) * h010111 + (1 / 3 : ℂ) * h001111

/-- Six-linear coefficients are determined by their 64 basis coordinates. -/
theorem basis_ext {f g : Coefficient}
    (h : ∀ i j k l m n, basisValue f i j k l m n = basisValue g i j k l m n) :
    f = g := by
  let b := Pi.basisFun ℂ (Fin 2)
  apply b.ext; intro i
  apply b.ext; intro j
  apply b.ext; intro k
  apply b.ext; intro l
  apply b.ext; intro m
  apply b.ext; intro n
  simp only [b, Pi.basisFun_apply]
  exact h i j k l m n

/-- Every invariant six-right-Weyl coefficient has basis coordinates in the
span of the five noncrossing epsilon pairings.  The coefficients are explicit
triangular combinations of five probes.  Together with `basis_ext`, this is a
tensor-level spanning statement. -/
theorem exists_pairing_coordinates (f : Coefficient) (hf : IsInvariant f) :
    ∃ c : Fin 5 → ℂ, ∀ i j k l m n,
      basisValue f i j k l m n = ∑ p, c p *
        pairingValue p (weakBasis i) (weakBasis j) (weakBasis k)
          (weakBasis l) (weakBasis m) (weakBasis n) := by
  let c : Fin 5 → ℂ := ![
    basisValue f 0 1 0 1 0 1 + basisValue f 0 1 0 0 1 1 +
      basisValue f 0 0 1 1 0 1 + basisValue f 0 0 1 0 1 1 +
      2 * basisValue f 0 0 0 1 1 1,
    basisValue f 0 1 0 0 1 1 + basisValue f 0 0 1 0 1 1 +
      basisValue f 0 0 0 1 1 1,
    basisValue f 0 0 1 1 0 1 + basisValue f 0 0 1 0 1 1 +
      basisValue f 0 0 0 1 1 1,
    basisValue f 0 0 1 0 1 1 + basisValue f 0 0 0 1 1 1,
    basisValue f 0 0 0 1 1 1]
  refine ⟨c, ?_⟩
  intro i j k l m n
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  rw [basisValue_formula f hf i j k l m n]
  simp [c]
  ring

end
end Physics.SixWeylInvariant
