import Math.Algebra.Constructions.FormalConnection
import Mathlib.Tactic

/-! Nonconstant unit gauge transformations in an ordinary differential algebra.
No action on a separately presented polynomial connection ring is assumed. -/
namespace Math.FormalConnection
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (P : Ordinary I A) (C : I → A)

theorem ordinary_one (i : I) : P.d i 1 = 0 := by
  have h := P.mul i 1 1
  have he : P.d i 1 + 0 = P.d i 1 + P.d i 1 := by simpa using h
  exact (add_left_cancel he).symm

theorem derivative_inverse (u : Aˣ) (i : I) :
    P.d i (↑u⁻¹ : A) = -((↑u⁻¹ : A) * P.d i (u : A) * ↑u⁻¹) := by
  have h := congrArg (fun x : A => (↑u⁻¹ : A) * x) (P.mul i (u : A) (↑u⁻¹ : A))
  simp only [Units.mul_inv, ordinary_one, mul_zero, mul_add] at h
  have hc (x : A) : (↑u⁻¹ : A) * ((u : A) * x) = x := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hc] at h
  exact eq_neg_of_add_eq_zero_right (by simpa only [mul_assoc] using h.symm)

def gauge (u : Aˣ) (i : I) : A :=
  (u : A) * C i * ↑u⁻¹ - P.d i (u : A) * ↑u⁻¹

theorem gauge_covariant (u : Aˣ) (i : I) (x : A) :
    covariant P (gauge P C u) i ((u : A) * x * ↑u⁻¹) =
      (u : A) * covariant P C i x * ↑u⁻¹ := by
  simp only [covariant_apply, gauge, bracket, P.mul, derivative_inverse]
  have hl (y : A) : (↑u⁻¹ : A) * ((u : A) * y) = y := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, mul_assoc, hl]
  noncomm_ring

theorem gauge_curvature (u : Aˣ) (i j : I) :
    curvature P (gauge P C u) i j = (u : A) * curvature P C i j * ↑u⁻¹ := by
  simp only [curvature, gauge, bracket, P.mul, map_sub, derivative_inverse]
  rw [P.commute i j (u : A)]
  have hl (y : A) : (↑u⁻¹ : A) * ((u : A) * y) = y := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, mul_assoc, hl]
  noncomm_ring

@[simp] theorem gauge_one : gauge P C 1 = C := by
  funext i
  simp [gauge, ordinary_one]

theorem gauge_composition (u v : Aˣ) : gauge P (gauge P C u) v = gauge P C (v * u) := by
  funext i
  simp only [gauge, Units.val_mul, mul_inv_rev, P.mul]
  have hc (x : A) : (u : A) * ((↑u⁻¹ : A) * x) = x := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  simp only [add_mul, mul_sub, sub_mul, mul_assoc, hc]
  noncomm_ring

def signedEquation [Fintype I] (s : I → ℂ) (j : I) : A :=
  ∑ i, s i • covariant P C i (curvature P C i j)

theorem gauge_equation [Fintype I] (s : I → ℂ) (u : Aˣ) (j : I) :
    signedEquation P (gauge P C u) s j = (u : A) * signedEquation P C s j * ↑u⁻¹ := by
  simp only [signedEquation, gauge_curvature, gauge_covariant, Finset.mul_sum,
    Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

end
end Math.FormalConnection
