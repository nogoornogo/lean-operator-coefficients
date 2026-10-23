import Math.Algebra.Jets.MixedJetAlgebra

/-! Word adjoints and explicit currents. These identities use an even Leibniz
rule and also hold in the noncommutative mixed exterior/polynomial algebra. -/
namespace Math.VariationalIBP
set_option autoImplicit false
noncomputable section
variable {A I : Type*} [Ring A] [Algebra ℂ A]
  (D : I → A →ₗ[ℂ] A)

def word : List I → A → A
  | [], p => p
  | i :: w, p => D i (word w p)

def adjoint : List I → A → A
  | [], p => p
  | i :: w, p => adjoint w (-D i p)

theorem adjoint_smul (w : List I) (c : ℂ) (p : A) :
    adjoint D w (c • p) = c • adjoint D w p := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp only [adjoint, map_smul, ← smul_neg, ih]

def divergence : (I →₀ A) →ₗ[ℂ] A := Finsupp.lsum ℂ D

@[simp] theorem divergence_single (i : I) (p : A) :
    divergence D (Finsupp.single i p) = D i p := Finsupp.lsum_single _ _ _ _

def current : List I → A → A → (I →₀ A)
  | [], _, _ => 0
  | i :: w, eta, p =>
    Finsupp.single i (word D w eta * p) + current w eta (-D i p)

theorem parts (leibniz : ∀ i p q, D i (p*q) = D i p*q + p*D i q)
    (w : List I) (eta p : A) :
    word D w eta * p = eta * adjoint D w p + divergence D (current D w eta p) := by
  induction w generalizing p with
  | nil => simp [word, adjoint, current]
  | cons i w ih =>
    simp only [word, adjoint, current, map_add, divergence_single, leibniz]
    have h := ih (-D i p)
    rw [mul_neg] at h
    rw [eq_sub_of_add_eq h.symm]
    abel

end
end Math.VariationalIBP
