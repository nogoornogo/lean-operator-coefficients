import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

/-! Formal adjoint connections over an associative algebra. All curvature
and Bianchi identities are derived, not included among the hypotheses. -/
namespace Math.FormalConnection
set_option autoImplicit false
noncomputable section

variable {A I : Type*} [Ring A] [Algebra ℂ A]

structure Ordinary (I A : Type*) [Ring A] [Algebra ℂ A] where
  d : I → A →ₗ[ℂ] A
  mul : ∀ i x y, d i (x * y) = d i x * y + x * d i y
  commute : ∀ i j x, d i (d j x) = d j (d i x)

variable (P : Ordinary I A) (C : I → A)

def bracket (x y : A) : A := x * y - y * x

def covariant (i : I) : A →ₗ[ℂ] A := P.d i +
  { toFun := fun x => bracket (C i) x
    map_add' := by intros; dsimp [bracket]; noncomm_ring
    map_smul' := by intros; simp [bracket, smul_sub] }

@[simp] theorem covariant_apply (i : I) (x : A) :
    covariant P C i x = P.d i x + bracket (C i) x := rfl

def curvature (i j : I) : A := P.d i (C j) - P.d j (C i) + bracket (C i) (C j)

theorem covariant_mul (i : I) (x y : A) :
    covariant P C i (x * y) = covariant P C i x * y + x * covariant P C i y := by
  simp only [covariant_apply, P.mul, bracket]
  noncomm_ring

theorem curvature_skew (i j : I) : curvature P C i j = -curvature P C j i := by
  dsimp [curvature, bracket]
  noncomm_ring

@[simp] theorem curvature_self (i : I) : curvature P C i i = 0 := by
  simp [curvature, bracket]

theorem covariant_commutator (i j : I) (x : A) :
    covariant P C i (covariant P C j x) - covariant P C j (covariant P C i x) =
      bracket (curvature P C i j) x := by
  simp only [covariant_apply, curvature, bracket, map_add, map_sub, P.mul]
  rw [P.commute i j x]
  noncomm_ring

theorem bianchi (i j k : I) :
    covariant P C i (curvature P C j k) + covariant P C j (curvature P C k i) +
      covariant P C k (curvature P C i j) = 0 := by
  simp only [covariant_apply, curvature, bracket, map_add, map_sub, P.mul]
  rw [P.commute i j (C k), P.commute j k (C i), P.commute k i (C j)]
  noncomm_ring

/-- Products of constant inverse matrices give a genuine covariance identity. -/
theorem conjugate_covariant (u v : A) (hvu : v * u = 1)
    (hdu : ∀ i, P.d i u = 0) (hdv : ∀ i, P.d i v = 0) (i : I) (x : A) :
    covariant P (fun j => u * C j * v) i (u * x * v) = u * covariant P C i x * v := by
  simp only [covariant_apply, P.mul, hdu, hdv, zero_mul, mul_zero, zero_add, add_zero,
    bracket]
  have hc (y : A) : v * (u * y) = y := by rw [← mul_assoc, hvu, one_mul]
  simp only [mul_assoc, hc]
  noncomm_ring

theorem conjugate_curvature (u v : A) (hvu : v * u = 1)
    (hdu : ∀ i, P.d i u = 0) (hdv : ∀ i, P.d i v = 0) (i j : I) :
    curvature P (fun k => u * C k * v) i j = u * curvature P C i j * v := by
  simp only [curvature, P.mul, hdu, hdv, zero_mul, mul_zero, zero_add, add_zero,
    bracket]
  have hc (y : A) : v * (u * y) = y := by rw [← mul_assoc, hvu, one_mul]
  simp only [mul_assoc, hc]
  noncomm_ring

end
end Math.FormalConnection
