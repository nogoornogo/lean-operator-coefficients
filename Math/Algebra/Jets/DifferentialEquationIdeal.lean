import Math.Algebra.Jets.ScalarJetGrading
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Polynomial equations and all derivative descendants. No linearity or
homogeneity of equations, nor commutation of derivatives, is assumed. -/
namespace Math.DifferentialEquation
set_option autoImplicit false
noncomputable section

variable {A I : Type*} [CommRing A] [Algebra ℂ A]
  (D : I → Derivation ℂ A A) (R : Set A)

def word : List I → A → A
  | [], p => p
  | i :: w, p => D i (word w p)

def ideal : Ideal A := Ideal.span {p | ∃ w r, r ∈ R ∧ word D w r = p}

theorem descendant_mem (w : List I) {r : A} (hr : r ∈ R) :
    word D w r ∈ ideal D R := Ideal.subset_span ⟨w, r, hr, rfl⟩

theorem seed_mem {r : A} (hr : r ∈ R) : r ∈ ideal D R := descendant_mem D R [] hr

theorem stable (i : I) {p : A} (hp : p ∈ ideal D R) : D i p ∈ ideal D R := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w, r, hr, rfl⟩ := hp
    exact descendant_mem D R (i :: w) hr
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using (ideal D R).add_mem ihp ihq
  | smul c p hp ih =>
    change D i (c * p) ∈ ideal D R
    rw [(D i).leibniz]
    exact (ideal D R).add_mem ((ideal D R).mul_mem_left _ ih)
      ((ideal D R).mul_mem_right _ hp)

theorem minimal (J : Ideal A) (hR : R ⊆ J)
    (hD : ∀ i p, p ∈ J → D i p ∈ J) : ideal D R ≤ J := by
  apply Ideal.span_le.mpr
  rintro p ⟨w, r, hr, rfl⟩
  induction w with
  | nil => exact hR hr
  | cons i w ih => exact hD i _ ih

theorem ideal_le_solution_kernel (f : A →ₐ[ℂ] ℂ) (hR : ∀ p ∈ R, f p = 0)
    (hD : ∀ i p, f (D i p) = 0) : ideal D R ≤ RingHom.ker f.toRingHom :=
  minimal D R _ hR (fun i p _ => hD i p)

theorem one_not_mem (f : A →ₐ[ℂ] ℂ) (hR : ∀ p ∈ R, f p = 0)
    (hD : ∀ i p, f (D i p) = 0) : (1 : A) ∉ ideal D R := by
  intro hp
  have h := ideal_le_solution_kernel D R f hR hD hp
  change f 1 = 0 at h
  exact one_ne_zero (by simpa only [map_one] using h)

abbrev Shell := A ⧸ ideal D R

def projection : A →ₐ[ℂ] Shell D R := Ideal.Quotient.mkₐ ℂ (ideal D R)

theorem projection_surjective : Function.Surjective (projection D R) :=
  Ideal.Quotient.mk_surjective

theorem projection_kernel : RingHom.ker (projection D R).toRingHom = ideal D R :=
  Ideal.mk_ker

@[simp] theorem projection_eq_zero (p : A) : projection D R p = 0 ↔ p ∈ ideal D R :=
  Ideal.Quotient.eq_zero_iff_mem

def derivative (i : I) : Derivation ℂ (Shell D R) (Shell D R) :=
  Derivation.liftOfSurjective (projection_surjective D R) (d := D i) (by
    intro p hp
    exact (projection_eq_zero D R _).mpr (stable D R i ((projection_eq_zero D R _).mp hp)))

@[simp] theorem derivative_projection (i : I) (p : A) :
    derivative D R i (projection D R p) = projection D R (D i p) :=
  by simp [derivative]

theorem derivative_commute (h : ∀ i j p, D i (D j p) = D j (D i p))
    (i j : I) (p : Shell D R) :
    derivative D R i (derivative D R j p) = derivative D R j (derivative D R i p) := by
  obtain ⟨p, rfl⟩ := projection_surjective D R p
  simp only [derivative_projection, h]

def relations : Submodule ℂ A := (ideal D R).restrictScalars ℂ

theorem linear_kernel : (projection D R).toLinearMap.ker = relations D R := by
  ext p
  exact projection_eq_zero D R p

def image (V : Submodule ℂ A) : Submodule ℂ (Shell D R) :=
  V.map (projection D R).toLinearMap

def imageProjection (V : Submodule ℂ A) : V →ₗ[ℂ] image D R V where
  toFun p := ⟨projection D R p.val, ⟨p.val, p.property, rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem imageProjection_surjective (V : Submodule ℂ A) :
    Function.Surjective (imageProjection D R V) := by
  rintro ⟨_, p, hp, rfl⟩
  exact ⟨⟨p, hp⟩, rfl⟩

instance image_finite (V : Submodule ℂ A) [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (image D R V) :=
  Module.Finite.of_surjective (imageProjection D R V) (imageProjection_surjective D R V)

/-- An explicit transport criterion; covariance of a physical model is not inferred. -/
theorem map_stable (f : A →ₐ[ℂ] A)
    (hR : ∀ p ∈ R, f p ∈ ideal D R)
    (hD : ∀ i p, f p ∈ ideal D R → f (D i p) ∈ ideal D R) :
    ∀ p ∈ ideal D R, f p ∈ ideal D R := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w, r, hr, rfl⟩ := hp
    induction w with
    | nil => exact hR r hr
    | cons i w ih => exact hD i _ ih
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using (ideal D R).add_mem ihp ihq
  | smul c p hp ih =>
    change f (c * p) ∈ ideal D R
    rw [map_mul]
    exact (ideal D R).mul_mem_left _ ih

end
end Math.DifferentialEquation

namespace Math.ScalarJetAlgebra
noncomputable section
open MvPolynomial
variable {S I : Type*}

def zeroEvaluation : Algebra S I →ₐ[ℂ] ℂ := aeval (fun _ => 0)

@[simp] theorem zeroEvaluation_X (j : Index S I) : zeroEvaluation (X j) = 0 := by
  simp [zeroEvaluation]

theorem zeroEvaluation_derivative (i : I) (p : Algebra S I) :
    zeroEvaluation (totalDerivative i p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp => simp [totalDerivative_X]

def constantEvaluation (v : S → ℂ) : Algebra S I →ₐ[ℂ] ℂ := by
  classical
  exact aeval (fun j => if j.2 = 0 then v j.1 else 0)

@[simp] theorem constantEvaluation_X_zero (v : S → ℂ) (s : S) :
    constantEvaluation (I := I) v (X (s, 0)) = v s := by simp [constantEvaluation]

theorem constantEvaluation_shift (v : S → ℂ) (i : I) (j : Index S I) :
    constantEvaluation v (X (shift i j)) = 0 := by
  have h : j.2 + Finsupp.single i 1 ≠ 0 := by
    intro he
    have hi := congrArg (fun a : I →₀ ℕ => a i) he
    simp at hi
  simp [constantEvaluation, shift, h]

theorem constantEvaluation_derivative (v : S → ℂ) (i : I) (p : Algebra S I) :
    constantEvaluation v (totalDerivative i p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    rw [totalDerivative_mul, totalDerivative_X, map_add, map_mul, map_mul, hp,
      constantEvaluation_shift]
    simp

end
end Math.ScalarJetAlgebra

namespace Math.DifferentialEquation
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [CommRing A] [Algebra ℂ A]
  (D : I → Derivation ℂ A A) (R : Set A)

def transport (f : A →ₐ[ℂ] A) (hf : ∀ p ∈ ideal D R, f p ∈ ideal D R) :
    Shell D R →ₐ[ℂ] Shell D R :=
  Ideal.Quotient.liftₐ (ideal D R) ((projection D R).comp f) (by
    intro p hp
    exact (projection_eq_zero D R _).mpr (hf p hp))

@[simp] theorem transport_projection (f : A →ₐ[ℂ] A)
    (hf : ∀ p ∈ ideal D R, f p ∈ ideal D R) (p : A) :
    transport D R f hf (projection D R p) = projection D R (f p) := rfl

end
end Math.DifferentialEquation
