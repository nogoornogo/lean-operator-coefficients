import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Determinant of a complex matrix exponential

Mathlib's matrix-exponential file currently leaves
`det (exp A) = exp (trace A)` as a TODO.  This file develops that identity as
the analytic input needed to send traceless skew-Hermitian matrices into the
special unitary group.
-/

namespace Math
namespace MatrixDeterminantExponential

noncomputable section

open NormedSpace
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
/-- The determinant is complex differentiable as a polynomial in the matrix
entries. -/
theorem differentiable_det :
    Differentiable ℂ (Matrix.det : Matrix n n ℂ → ℂ) := by
  classical
  intro A
  change DifferentiableAt ℂ (fun B : Matrix n n ℂ ↦ Matrix.det B) A
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _hσ
  apply DifferentiableAt.const_mul
  have hEntry : ∀ i : n,
      DifferentiableAt ℂ (fun B : Matrix n n ℂ ↦ B (σ i) i) A := by
    intro i
    fun_prop
  convert!
    (HasFDerivAt.finsetProd (u := Finset.univ)
      (fun i _hi ↦ (hEntry i).hasFDerivAt)).differentiableAt using 1

set_option backward.isDefEq.respectTransparency false in
/-- The derivative at zero of `t ↦ det (1 + t A)` is `trace A`. -/
theorem hasDerivAt_det_one_add_smul (A : Matrix n n ℂ) :
    HasDerivAt (fun t : ℂ ↦ Matrix.det (1 + t • A)) (Matrix.trace A) 0 := by
  let p : Polynomial ℂ :=
    (Matrix.det
      (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).divX.divX
  have hLinear : HasDerivAt
      (fun t : ℂ ↦ 1 + Matrix.trace A * t) (Matrix.trace A) 0 := by
    convert!
      (hasDerivAt_const_mul (x := (0 : ℂ)) (Matrix.trace A)).const_add 1 using 1
  have hSquare : HasDerivAt (fun t : ℂ ↦ t ^ 2) 0 0 := by
    convert! hasDerivAt_pow 2 (0 : ℂ) using 1
    norm_num
  have hRemainder : HasDerivAt (fun t : ℂ ↦ p.eval t * t ^ 2) 0 0 := by
    convert! (p.hasDerivAt 0).mul hSquare using 1
    simp
  have hRight : HasDerivAt
      (fun t : ℂ ↦ 1 + Matrix.trace A * t + p.eval t * t ^ 2)
      (Matrix.trace A) 0 := by
    convert! hLinear.add hRemainder using 1
    simp
  apply hRight.congr_of_eventuallyEq
  filter_upwards [] with t
  simpa [p] using Matrix.det_one_add_smul t A

/-- The continuous linear trace map, used as the derivative of the
determinant at the identity matrix. -/
noncomputable def traceContinuousLinearMap :
    Matrix n n ℂ →L[ℂ] ℂ :=
  { Matrix.traceLinearMap n ℂ ℂ with
    cont := LinearMap.continuous_of_finiteDimensional _ }

omit [DecidableEq n] in
@[simp]
theorem traceContinuousLinearMap_apply (A : Matrix n n ℂ) :
    traceContinuousLinearMap A = Matrix.trace A :=
  rfl

/-- The Frechet derivative of the determinant at the identity matrix is the
trace. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (Matrix.det : Matrix n n ℂ → ℂ)
      traceContinuousLinearMap 1 := by
  have hDet := (differentiable_det (n := n) 1).hasFDerivAt
  apply hDet.congr_fderiv
  apply ContinuousLinearMap.ext
  intro A
  have hAffine : HasDerivAt
      (fun t : ℂ ↦ (1 : Matrix n n ℂ) + t • A) A 0 := by
    convert!
      ((hasDerivAt_id' (0 : ℂ)).smul_const A).const_add
        (1 : Matrix n n ℂ) using 1
    simp
  have hLine := hDet.comp_hasDerivAt_of_eq 0 hAffine (by simp)
  have hExpected := hasDerivAt_det_one_add_smul A
  convert hLine.unique hExpected using 1 ; rfl

set_option backward.isDefEq.respectTransparency false in
/-- At the origin, the determinant of the matrix-exponential line has
derivative `trace A`. -/
theorem hasDerivAt_det_exp_smul_zero (A : Matrix n n ℂ) :
    HasDerivAt
      (fun t : ℂ ↦ Matrix.det (exp (t • A))) (Matrix.trace A) 0 := by
  have hDet : HasFDerivAt
      (Matrix.det : Matrix n n ℂ → ℂ)
      (fderiv ℂ (Matrix.det : Matrix n n ℂ → ℂ) 1) 1 :=
    (differentiable_det (n := n) 1).hasFDerivAt
  have hAffine : HasDerivAt
      (fun t : ℂ ↦ (1 : Matrix n n ℂ) + t • A) A 0 := by
    convert!
      ((hasDerivAt_id' (0 : ℂ)).smul_const A).const_add
        (1 : Matrix n n ℂ) using 1
    simp
  have hLine := hDet.comp_hasDerivAt_of_eq 0 hAffine (by simp)
  have hFderiv :
      (fderiv ℂ (Matrix.det : Matrix n n ℂ → ℂ) 1) A =
        Matrix.trace A := by
    exact hLine.unique (hasDerivAt_det_one_add_smul A)
  have hExp : HasDerivAt
      (fun t : ℂ ↦ exp (t • A)) A 0 := by
    convert! hasDerivAt_exp_smul_const A (0 : ℂ) using 1
    simp
  have hComposite := hDet.comp_hasDerivAt_of_eq 0 hExp (by simp)
  convert! hComposite.congr_deriv hFderiv using 1

/-- The determinant of a matrix-exponential line is multiplicative in its
scalar parameter. -/
theorem det_exp_add_smul (A : Matrix n n ℂ) (s t : ℂ) :
    Matrix.det (exp ((s + t) • A)) =
      Matrix.det (exp (s • A)) * Matrix.det (exp (t • A)) := by
  rw [add_smul]
  rw [Matrix.exp_add_of_commute]
  · exact Matrix.det_mul _ _
  · exact ((Commute.refl A).smul_left s).smul_right t

set_option backward.isDefEq.respectTransparency false in
/-- At every parameter, the determinant of the matrix-exponential line has
the logarithmic derivative `trace A`. -/
theorem hasDerivAt_det_exp_smul (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt
      (fun s : ℂ ↦ Matrix.det (exp (s • A)))
      (Matrix.det (exp (t • A)) * Matrix.trace A) t := by
  let h : ℂ → ℂ := fun s ↦ Matrix.det (exp (s • A))
  have hZero : HasDerivAt h (Matrix.trace A) 0 := by
    exact hasDerivAt_det_exp_smul_zero A
  have hScaled : HasDerivAt
      (fun s : ℂ ↦ h t * h s) (h t * Matrix.trace A) 0 :=
    hZero.const_mul (h t)
  have hShift : HasDerivAt
      (fun s : ℂ ↦ h (t + s)) (h t * Matrix.trace A) 0 := by
    apply hScaled.congr_of_eventuallyEq
    filter_upwards [] with s
    exact det_exp_add_smul A t s
  have hTranslate : HasDerivAt (fun s : ℂ ↦ s - t) 1 t :=
    (hasDerivAt_id' t).sub_const t
  have hAt := hShift.comp_of_eq t hTranslate (by simp)
  have hFunction :
      ((fun s : ℂ ↦ h (t + s)) ∘ fun s : ℂ ↦ s - t) = h := by
    funext s
    simp
  rw [hFunction] at hAt
  convert! hAt using 1
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the determinant exponential line by the inverse scalar
exponential gives a function with zero derivative. -/
theorem hasDerivAt_det_exp_smul_mul_exp_neg_trace
    (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt
      (fun s : ℂ ↦
        Matrix.det (exp (s • A)) *
          Complex.exp ((-Matrix.trace A) * s)) 0 t := by
  have hDet := hasDerivAt_det_exp_smul A t
  have hLinear : HasDerivAt
      (fun s : ℂ ↦ (-Matrix.trace A) * s) (-Matrix.trace A) t :=
    hasDerivAt_const_mul (-Matrix.trace A)
  have hScalarExp : HasDerivAt
      (fun s : ℂ ↦ Complex.exp ((-Matrix.trace A) * s))
      (Complex.exp ((-Matrix.trace A) * t) * (-Matrix.trace A)) t :=
    (Complex.hasDerivAt_exp ((-Matrix.trace A) * t)).comp t hLinear
  have hProduct := hDet.mul hScalarExp
  apply hProduct.congr_deriv
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of a finite complex matrix exponential is the scalar
exponential of its trace. -/
theorem det_exp (A : Matrix n n ℂ) :
    Matrix.det (exp A) = Complex.exp (Matrix.trace A) := by
  let q : ℂ → ℂ := fun t ↦
    Matrix.det (exp (t • A)) *
      Complex.exp ((-Matrix.trace A) * t)
  have hq : ∀ t : ℂ, HasDerivAt q 0 t := by
    intro t
    exact hasDerivAt_det_exp_smul_mul_exp_neg_trace A t
  have hqDifferentiable : Differentiable ℂ q := fun t ↦
    (hq t).differentiableAt
  have hqDeriv : ∀ t : ℂ, deriv q t = 0 := fun t ↦ (hq t).deriv
  have hConstant : q 1 = q 0 :=
    is_const_of_deriv_eq_zero hqDifferentiable hqDeriv 1 0
  have hOne :
      Matrix.det (exp A) * Complex.exp (-Matrix.trace A) = 1 := by
    simpa [q] using hConstant
  have hInverse :
      Complex.exp (-Matrix.trace A) * Complex.exp (Matrix.trace A) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    Matrix.det (exp A) = Matrix.det (exp A) * 1 := by simp
    _ = Matrix.det (exp A) *
        (Complex.exp (-Matrix.trace A) * Complex.exp (Matrix.trace A)) := by
          rw [hInverse]
    _ = (Matrix.det (exp A) * Complex.exp (-Matrix.trace A)) *
        Complex.exp (Matrix.trace A) := by ring
    _ = Complex.exp (Matrix.trace A) := by rw [hOne, one_mul]

end

end MatrixDeterminantExponential
end Math
