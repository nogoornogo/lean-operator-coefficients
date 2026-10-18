import Math.LieGroups.E6.Minuscule.CompactCenter
import Math.LieGroups.E6.Minuscule.NormalizerCenter
import Math.LieGroups.E6.Minuscule.D5Blocks
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! An actual order-three scalar in the compact candidate, constructed by
exponentiating its Cartan grading. This is a lower bound, not an exact
center computation or a simple-connectedness theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

def gradingDirection : compactMatrixLieAlgebra :=
  ∑ i : Fin 6, (gradingCoefficients i : ℝ) • compactMatrixEquiv (compactGeneratorElement 2 i)

theorem gradingDirection_matrix :
    (gradingDirection : Matrix27) = Matrix.diagonal (fun a => Complex.I * (grade a : ℂ)) := by
  ext a b
  change (∑ i : Fin 6, (gradingCoefficients i : ℝ) • compactH i) a b = _
  by_cases h : a = b
  · subst b
    simp [compactH, cartan, grade, Matrix.sum_apply, Int.cast_sum, Int.cast_mul,
      RCLike.real_smul_eq_coe_mul, Finset.mul_sum, mul_comm, mul_assoc]
  · simp [compactH, cartan, h, Matrix.sum_apply]

def centerThirdDirection : compactMatrixLieAlgebra := (2 * Real.pi / 3) • gradingDirection

theorem centerThirdDirection_matrix : (centerThirdDirection : Matrix27) =
    Matrix.diagonal (fun a => (grade a : ℂ) * (2 * Real.pi * Complex.I / 3)) := by
  change ((2 * Real.pi / 3) • (gradingDirection : Matrix27)) = _
  rw [gradingDirection_matrix]
  ext a b
  by_cases h : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, RCLike.real_smul_eq_coe_mul]
    change ((2 * Real.pi / 3 : ℝ) : ℂ) * (Complex.I * (grade a : ℂ)) = _
    push_cast
    ring
  · simp [h]

def scalarRoot3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem scalarRoot3_primitive : IsPrimitiveRoot scalarRoot3 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

theorem scalarRoot3_ne_one : scalarRoot3 ≠ 1 := scalarRoot3_primitive.ne_one (by decide)

theorem exp_graded_entry (a : Fin 27) :
    Complex.exp ((grade a : ℂ) * (2 * Real.pi * Complex.I / 3)) = scalarRoot3 := by
  rw [Complex.exp_int_mul]
  change scalarRoot3 ^ grade a = scalarRoot3
  rcases grade_values a with h | h | h
  · simp [h]
  · have hn : scalarRoot3 ≠ 0 := Complex.exp_ne_zero _
    have hp := scalarRoot3_primitive.pow_eq_one
    rw [h]
    simp only [zpow_neg, zpow_ofNat]
    apply (mul_left_injective₀ (pow_ne_zero 2 hn))
    dsimp
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hn)]
    simpa only [pow_succ, mul_comm] using hp.symm
  · rw [h]
    simp only [zpow_ofNat, show (4 : ℕ) = 3 + 1 from rfl, pow_succ,
      scalarRoot3_primitive.pow_eq_one, one_mul]

theorem exp_centerThirdDirection :
    exp (centerThirdDirection : Matrix27) = scalarRoot3 • (1 : Matrix27) := by
  rw [centerThirdDirection_matrix, Matrix.exp_diagonal]
  have he : exp (fun a : Fin 27 => (grade a : ℂ) * (2 * Real.pi * Complex.I / 3)) =
      fun _ => scalarRoot3 := by
    funext a
    rw [Pi.coe_exp]
    simpa only [← Complex.exp_eq_exp_ℂ] using exp_graded_entry a
  rw [he]
  ext a b
  by_cases h : a = b <;> simp [h]

def centralScalar3 : compactIdentityComponent := compactExp centerThirdDirection

@[simp] theorem centralScalar3_matrix : compactMatrix centralScalar3 = scalarRoot3 • 1 :=
  (compactExp_coe centerThirdDirection).trans exp_centerThirdDirection

theorem centralScalar3_mem_center : centralScalar3 ∈ Subgroup.center compactIdentityComponent :=
  (compact_mem_center_iff_scalar _).mpr ⟨scalarRoot3, centralScalar3_matrix⟩

theorem centralScalar3_pow_matrix (k : ℕ) :
    compactMatrix (centralScalar3 ^ k) = scalarRoot3 ^ k • 1 := by
  induction k with
  | zero => simp
  | succ k hk => simp [pow_succ, compactMatrix_mul, hk, smul_smul, mul_comm]

theorem centralScalar3_pow_eq_one_iff (k : ℕ) : centralScalar3 ^ k = 1 ↔ 3 ∣ k := by
  rw [← scalarRoot3_primitive.pow_eq_one_iff_dvd k]
  constructor
  · intro h
    have hm := congrArg compactMatrix h
    rw [centralScalar3_pow_matrix, compactMatrix_one] at hm
    simpa using congrArg (fun A : Matrix27 => A 0 0) hm
  · intro h
    apply compactMatrix_injective
    simp [centralScalar3_pow_matrix, h]

theorem centralScalar3_orderOf : orderOf centralScalar3 = 3 :=
  Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one ((centralScalar3_pow_eq_one_iff 3).mpr (dvd_refl 3)))
    ((centralScalar3_pow_eq_one_iff _).mp (pow_orderOf_eq_one centralScalar3))

def centerElement3 : Subgroup.center compactIdentityComponent :=
  ⟨centralScalar3, centralScalar3_mem_center⟩

theorem centerElement3_orderOf : orderOf centerElement3 = 3 := by
  rw [← centralScalar3_orderOf]
  exact (orderOf_injective (Subgroup.center compactIdentityComponent).subtype
    Subtype.val_injective centerElement3).symm

theorem three_dvd_compactCenter_card : 3 ∣ Nat.card (Subgroup.center compactIdentityComponent) := by
  rw [← centerElement3_orderOf]
  exact orderOf_dvd_natCard centerElement3

theorem compactCenter_card_bounds :
    3 ∣ Nat.card (Subgroup.center compactIdentityComponent) ∧
      Nat.card (Subgroup.center compactIdentityComponent) ∣ 27 :=
  ⟨three_dvd_compactCenter_card, compactCenter_card_dvd⟩

theorem scalarRoot27_pow_nine : scalarRoot27 ^ 9 = scalarRoot3 := by
  rw [scalarRoot27, ← Complex.exp_nat_mul, scalarRoot3]
  congr 1
  norm_num
  ring

theorem centralScalar3_val : centralScalar3.val = centralScalar27 ^ 9 := by
  apply Subtype.ext
  apply Subtype.ext
  change compactMatrix centralScalar3 = ((centralScalar27 ^ 9).val : Matrix27)
  rw [centralScalar3_matrix, centralScalar27_pow_coe, scalarRoot27_pow_nine]

theorem centralScalar27_pow_nine_mem : centralScalar27 ^ 9 ∈ compactIdentityComponent := by
  rw [← centralScalar3_val]
  exact centralScalar3.property

end

end Math.E6.Minuscule
