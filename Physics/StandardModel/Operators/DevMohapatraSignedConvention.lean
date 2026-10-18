import Physics.StandardModel.Operators.DevMohapatraTreeLevel
import Physics.FieldTheory.Spinor.RightWeylChargeConjugation

/-! Explicit supplied Euclidean inverse-C convention, not a recovered source convention. -/
namespace GUT.DevMohapatraSignedConvention
set_option autoImplicit false
noncomputable section
open DevMohapatraTreeLevel RightWeylChargeConjugation
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def inverseCharge : Matrix (Fin 4) (Fin 4) ℂ := -charge

theorem inverse_left : inverseCharge * charge = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [inverseCharge, charge, Matrix.mul_apply, Fin.sum_univ_succ]

theorem inverse_right : charge * inverseCharge = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [inverseCharge, charge, Matrix.mul_apply, Fin.sum_univ_succ]

def components (x : Fin 2 → V) : Fin 4 → A V :=
  ![ExteriorAlgebra.ι ℂ (x 0), ExteriorAlgebra.ι ℂ (x 1), 0, 0]

def inversePair (x y : Fin 2 → V) : A V :=
  ∑ i, ∑ j, (inverseCharge * rightProjector) i j • (components x i * components y j)

theorem inversePair_eq (x y : Fin 2 → V) : inversePair x y = -pair x y := by
  simp [inversePair, inverseCharge, charge, rightProjector, components, pair,
    Matrix.mul_apply, Fin.sum_univ_succ, sub_eq_add_neg]
  abel

theorem source_mass (m : ℂ) (n : Fin 2 → V) :
    (m / 2) • inversePair n n = -m •
      (ExteriorAlgebra.ι ℂ (n 0) * ExteriorAlgebra.ι ℂ (n 1)) := by
  rw [inversePair_eq, smul_neg]
  simpa only [neg_smul] using majorana_half m n

theorem source_vertex (z : ℂ) (x y : Fin 2 → V) :
    z • inversePair x y = (-z) • pair x y := by rw [inversePair_eq, smul_neg, neg_smul]

def inverseDownCurrent (d s : Fin 3 → Fin 2 → V) (a : Fin 3) : A V :=
  ∑ b, ∑ c, SMEpsilonTensor.eps3 (SMEpsilonTensor.colorBasis a)
    (SMEpsilonTensor.colorBasis b) (SMEpsilonTensor.colorBasis c) • inversePair (d b) (s c)

theorem inverseDownCurrent_eq (d s : Fin 3 → Fin 2 → V) (a : Fin 3) :
    inverseDownCurrent d s a = -downCurrent d s a := by
  simp [inverseDownCurrent, inversePair_eq, downCurrent]

/-- Three inverse-C bilinears multiply the literal epsilon target by minus one. -/
def inverseOperator (u d s : Fin 3 → Fin 2 → V) : A V :=
  ∑ a, ∑ b, inversePair (u a) (u b) *
    (inverseDownCurrent d s a * inverseDownCurrent d s b)

theorem inverseOperator_eq (u d s : Fin 3 → Fin 2 → V) :
    inverseOperator u d s = -printedOperator u d s := by
  simp [inverseOperator, inversePair_eq, inverseDownCurrent_eq, printedOperator]

theorem generated_inverse (m M lam b : ℂ) (u d s : Fin 3 → Fin 2 → V) :
    generated m M (-lam) (-b) u d s =
      (-treePrefactor m M lam b) • inverseOperator u d s := by
  rw [generated_printed, inverseOperator_eq]
  simp only [treePrefactor, neg_mul_neg, neg_smul, smul_neg, neg_neg]

/-- Rescale every bilinear: mass and both vertices acquire c, target acquires c^3. -/
theorem consistent_bilinear_rescaling (m M lam b c : ℂ) (hc : c ≠ 0) (hM : M ≠ 0) :
    treePrefactor m (c * M) (c * lam) (c * b) = c ^ 3 * treePrefactor m M lam b := by
  unfold treePrefactor
  simp only [div_eq_mul_inv, mul_inv_rev, mul_pow]
  field_simp [hc, hM]

end
end GUT.DevMohapatraSignedConvention
