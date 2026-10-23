import Math.LinearAlgebra.Matrix.UnitaryDiagonalCongruence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Circle

/-! Phase normalization of specified diagonal complex bilinear coefficients. -/
namespace Math.MajoranaPhaseNormalization
set_option autoImplicit false
noncomputable section
open Matrix UnitaryDiagonalCongruence
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_phase (c : ℂ) : ∃ p : Circle, c * (p : ℂ) ^ 2 = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · subst c; exact ⟨1, by simp⟩
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq ((‖c‖ : ℂ) / c) (by decide : 0 < 2)
  have hn : ‖p‖ = 1 := by
    have hh := congrArg norm hp
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c), div_self (norm_ne_zero_iff.mpr hc)] at hh
    nlinarith [norm_nonneg p]
  exact ⟨⟨p, by simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hn⟩,
    by change c * p ^ 2 = _; rw [hp]; field_simp⟩

def phase (c : I → ℂ) (i : I) : Circle := by
  classical
  exact if c i = 0 then 1 else (exists_phase (c i)).choose

omit [Fintype I] [DecidableEq I] in
theorem phase_spec (c : I → ℂ) (i : I) :
    c i * (phase c i : ℂ) ^ 2 = (‖c i‖ : ℂ) := by
  classical
  by_cases hc : c i = 0
  · simp [phase, hc]
  · simpa only [phase, ite_eq_right hc] using (exists_phase (c i)).choose_spec

omit [Fintype I] [DecidableEq I] in
theorem phase_zero (c : I → ℂ) (i : I) (hc : c i = 0) : phase c i = 1 := by
  simp [phase, hc]

def diagonalPhase (p : I → Circle) : unitaryGroup I ℂ :=
  ⟨diagonal (fun i => (p i : ℂ)), by
    rw [mem_unitaryGroup_iff]
    have hs : star (diagonal (fun i => (p i : ℂ))) = diagonal (fun i => star (p i : ℂ)) := by
      simp [star_eq_conjTranspose]
    rw [hs, diagonal_mul_diagonal']
    have he : (fun i => (p i : ℂ) * star (p i : ℂ)) = fun i => 1 := by
      funext i
      simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj, Circle.coe_one, Complex.star_def] using
        congrArg (fun z : Circle => (z : ℂ)) (mul_inv_cancel (p i))
    rw [he, diagonal_one]⟩

theorem diagonalPhase_spec (c : I → ℂ) :
    (diagonalPhase (phase c)).val.transpose * diagonal c * (diagonalPhase (phase c)).val =
      diagonal (fun i => (‖c i‖ : ℂ)) := by
  simp only [diagonalPhase, diagonal_transpose, diagonal_mul_diagonal']
  congr 1
  funext i
  calc
    _ = c i * (phase c i : ℂ) ^ 2 := by ring
    _ = _ := phase_spec c i

theorem undo_congruence (c d : I → ℂ) (P : unitaryGroup I ℂ)
    (hP : P.val.transpose * diagonal c * P.val = diagonal d) :
    (P⁻¹).val.transpose * diagonal d * (P⁻¹).val = diagonal c := by
  rw [← hP]
  have hi : P.val * (P⁻¹).val = 1 := congrArg (fun U : unitaryGroup I ℂ => U.val) (mul_inv_cancel P)
  calc
    _ = (P.val * (P⁻¹).val).transpose * diagonal c * (P.val * (P⁻¹).val) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hi]; simp

theorem conjugate_preserves (c d : I → ℂ) (P U : unitaryGroup I ℂ)
    (hP : P.val.transpose * diagonal c * P.val = diagonal d)
    (hU : Preserves d U.val) : Preserves c (P * U * P⁻¹).val := by
  change (P.val * U.val * (P⁻¹).val).transpose * diagonal c *
    (P.val * U.val * (P⁻¹).val) = diagonal c
  calc
    _ = (P⁻¹).val.transpose * (U.val.transpose *
        (P.val.transpose * diagonal c * P.val) * U.val) * (P⁻¹).val := by
      simp only [transpose_mul, Matrix.mul_assoc]
    _ = (P⁻¹).val.transpose * diagonal d * (P⁻¹).val := by rw [hP, hU]
    _ = _ := undo_congruence c d P hP

def congruenceEquiv (c d : I → ℂ) (P : unitaryGroup I ℂ)
    (hP : P.val.transpose * diagonal c * P.val = diagonal d) : subgroup d ≃* subgroup c where
  toFun U := ⟨P * U.val * P⁻¹, conjugate_preserves c d P U.val hP U.property⟩
  invFun U := ⟨P⁻¹ * U.val * P, by
    change Preserves d (P⁻¹ * U.val * P).val
    simpa using conjugate_preserves d c P⁻¹ U.val (undo_congruence c d P hP) U.property⟩
  left_inv U := by apply Subtype.ext; simp [mul_assoc]
  right_inv U := by apply Subtype.ext; simp [mul_assoc]
  map_mul' U V := by apply Subtype.ext; simp [mul_assoc]

def normalizationEquiv (c : I → ℂ) :
    subgroup c ≃* subgroup (fun i => (‖c i‖ : ℂ)) :=
  (congruenceEquiv c _ (diagonalPhase (phase c)) (diagonalPhase_spec c)).symm

end
end Math.MajoranaPhaseNormalization
