import Math.LieGroups.E6.Minuscule.CompactTorus
import Math.LieGroups.Matrix.RotationExponential

/-! Actual rank-one rotations used to fill the six Cartan loops. The finite
checks concern matrices only; the exponential equalities are analytic. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Math.E6.Minuscule.Coroot

open SparseMatrixCertificate LieData TauCeti.E6Minuscule NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

private def xCode (i : Fin 6) : Code (Fin 27) :=
  e6Basis ⟨i.val, by omega⟩ ++ scale (-1) (e6Basis ⟨i.val + 6, by omega⟩)

private def hCode (i : Fin 6) : Code (Fin 27) := e6Basis ⟨i.val + 12, by omega⟩

private def identityCode : Code (Fin 27) := List.ofFn fun a : Fin 27 => ((a, a), (1 : ℤ))

private def jCode (i : Fin 6) : Code (Fin 27) :=
  identityCode ++ xCode i ++ mul (xCode i) (xCode i)

set_option maxRecDepth 16000 in
private theorem checked (i : Fin 6) :
    checkEq (mul (mul (xCode i) (xCode i)) (xCode i)) (scale (-1) (xCode i)) = true ∧
    checkEq (mul (mul (hCode i) (hCode i)) (hCode i)) (hCode i) = true ∧
    checkEq (mul (xCode i) (xCode i)) (scale (-1) (mul (hCode i) (hCode i))) = true ∧
    checkEq (mul (jCode i) (hCode i)) (scale (-1) (mul (hCode i) (jCode i))) = true := by
  decide +kernel +revert

private theorem eval_x (i : Fin 6) : eval (xCode i) = raisingMatrix i - loweringMatrix i := by
  decide +kernel +revert

private theorem eval_h (i : Fin 6) : eval (hCode i) = cartanGeneratorMatrix i := by
  decide +kernel +revert

private theorem eval_identity : eval identityCode = 1 := by decide +kernel

noncomputable section

private def castMatrix : Matrix (Fin 27) (Fin 27) ℤ →+* Matrix27 :=
  (Int.castRingHom ℂ).mapMatrix

private theorem cast_x (i : Fin 6) : castMatrix (eval (xCode i)) = compactX i := by
  rw [eval_x, map_sub]
  rfl

private theorem cast_h (i : Fin 6) : castMatrix (eval (hCode i)) = cartan i := by
  rw [eval_h]
  rfl

private theorem cast_j (i : Fin 6) : castMatrix (eval (jCode i)) =
    1 + compactX i + compactX i ^ 2 := by
  simp only [jCode, eval_append, eval_identity, eval_mul, map_add, map_one, map_mul,
    cast_x, pow_two]

theorem x_cube (i : Fin 6) : compactX i ^ 3 = -compactX i := by
  have h := congrArg castMatrix (checkEq_sound _ _ (checked i).1)
  simpa only [eval_mul, eval_scale, neg_one_zsmul, map_mul, map_neg, cast_x,
    pow_succ, pow_zero, one_mul] using h

theorem cartan_cube (i : Fin 6) : cartan i ^ 3 = cartan i := by
  have h := congrArg castMatrix (checkEq_sound _ _ (checked i).2.1)
  simpa only [eval_mul, map_mul, cast_h, pow_succ, pow_zero, one_mul] using h

theorem x_square (i : Fin 6) : compactX i ^ 2 = -(cartan i ^ 2) := by
  have h := congrArg castMatrix (checkEq_sound _ _ (checked i).2.2.1)
  simpa only [eval_mul, eval_scale, neg_one_zsmul, map_mul, map_neg, cast_x, cast_h,
    pow_two] using h

theorem quarter_anticommutes (i : Fin 6) :
    (1 + compactX i + compactX i ^ 2) * compactH i =
      -(compactH i) * (1 + compactX i + compactX i ^ 2) := by
  have h := congrArg castMatrix (checkEq_sound _ _ (checked i).2.2.2)
  simp only [eval_mul, eval_scale, neg_one_zsmul, map_mul, map_neg, cast_j, cast_h] at h
  simpa only [compactH, mul_smul_comm, smul_mul_assoc, smul_neg, neg_mul] using
    congrArg (fun M : Matrix27 => Complex.I • M) h

theorem h_cube (i : Fin 6) : compactH i ^ 3 = -compactH i := by
  have hi : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq, neg_one_mul]
  simp only [compactH, smul_pow, cartan_cube, hi, neg_smul]

theorem h_square (i : Fin 6) : compactH i ^ 2 = compactX i ^ 2 := by
  simp only [compactH, smul_pow, Complex.I_sq, neg_one_smul, x_square]

theorem exp_h_pi (i : Fin 6) : exp (Real.pi • compactH i) =
    1 + (2 : ℝ) • compactX i ^ 2 := by
  rw [RotationExponential.exp_eq_rotation _ (h_cube i)]
  norm_num [RotationExponential.rotation, h_square]

theorem exp_h_two_pi (i : Fin 6) : exp ((2 * Real.pi) • compactH i) = 1 := by
  rw [RotationExponential.exp_eq_rotation _ (h_cube i)]
  simp [RotationExponential.rotation]

theorem exp_x_half_pi (i : Fin 6) : exp ((Real.pi / 2) • compactX i) =
    1 + compactX i + compactX i ^ 2 := by
  rw [RotationExponential.exp_eq_rotation _ (x_cube i)]
  simp [RotationExponential.rotation]

theorem half_period_commutes (i : Fin 6) (t : ℝ) :
    Commute (exp (Real.pi • compactH i)) (exp (t • compactX i)) := by
  rw [exp_h_pi]
  exact ((Commute.one_left _).add_left ((Commute.pow_self _ 2).smul_left (2 : ℝ))).smul_right t
    |>.exp_right

theorem quarter_turn (i : Fin 6) (t : ℝ) :
    exp (t • compactH i) * exp ((Real.pi / 2) • compactX i) * exp (t • compactH i) =
      exp ((Real.pi / 2) • compactX i) := by
  let := NormedAlgebra.restrictScalars ℚ ℂ Matrix27
  have h : SemiconjBy (exp ((Real.pi / 2) • compactX i)) (t • compactH i)
      (-(t • compactH i)) := by
    rw [exp_x_half_pi]
    simpa only [SemiconjBy, mul_smul_comm, smul_mul_assoc, smul_neg, neg_mul] using
      congrArg (fun M : Matrix27 => t • M) (quarter_anticommutes i)
  simpa only [neg_neg] using h.exp_neg_mul_mul_exp_eq_self

end

end Math.E6.Minuscule.Coroot
