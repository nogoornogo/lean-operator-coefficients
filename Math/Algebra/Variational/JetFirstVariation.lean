import Math.Algebra.Jets.ScalarJetAlgebra
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Evolutionary variations on the full four-direction jet polynomial algebra,
and actual epsilon substitutions with their zeroth/first coefficients. -/
namespace Math.JetFirstVariation
set_option autoImplicit false
noncomputable section
open ScalarJetAlgebra MvPolynomial
variable {S : Type*}
abbrev Poly (S : Type*) := ScalarJetAlgebra.Algebra S (Fin 4)
abbrev D := ScalarJetAlgebra.totalDerivative (S := S) (I := Fin 4)

theorem derivative_iterate (i j : Fin 4) (n : ℕ) (p : Poly S) :
    D i ((D j : Poly S → Poly S)^[n] p) = (D j : Poly S → Poly S)^[n] (D i p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ScalarJetAlgebra.totalDerivative_commute, ih]

def prolong (eta : S → Poly S) (s : S) (a : Fin 4 →₀ ℕ) : Poly S :=
  (D 0 : Poly S → Poly S)^[a 0]
    ((D 1 : Poly S → Poly S)^[a 1]
      ((D 2 : Poly S → Poly S)^[a 2] ((D 3 : Poly S → Poly S)^[a 3] (eta s))))

@[simp] theorem prolong_zero (eta : S → Poly S) (s : S) : prolong eta s 0 = eta s := by
  simp [prolong]

theorem prolong_shift (eta : S → Poly S) (s : S) (a : Fin 4 →₀ ℕ) (i : Fin 4) :
    prolong eta s (a + Finsupp.single i 1) = D i (prolong eta s a) := by
  fin_cases i <;>
    simp [prolong, Finsupp.add_apply, Fin.ext_iff,
      Function.iterate_succ_apply', derivative_iterate]

def variation (eta : S → Poly S) : Derivation ℂ (Poly S) (Poly S) :=
  MvPolynomial.mkDerivation ℂ (fun j => prolong eta j.1 j.2)

@[simp] theorem variation_X (eta : S → Poly S) (j : Index S (Fin 4)) :
    variation eta (X j) = prolong eta j.1 j.2 := by simp [variation]

@[simp] theorem variation_field (eta : S → Poly S) (s : S) :
    variation eta (X (s, 0)) = eta s := by simp

theorem variation_derivative (eta : S → Poly S) (i : Fin 4) (p : Poly S) :
    variation eta (D i p) = D i (variation eta p) := by
  have h : ⁅D (S := S) i, variation eta⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    simp only [Derivation.commutator_apply, variation_X, totalDerivative_X,
      ScalarJetAlgebra.shift, prolong_shift, sub_self]
    rfl
  exact (sub_eq_zero.mp (DFunLike.congr_fun h p)).symm

def substitution (eta : S → Poly S) : Poly S →ₐ[ℂ] Polynomial (Poly S) :=
  aeval (fun j => Polynomial.C (X j) + Polynomial.C (variation eta (X j)) * Polynomial.X)

@[simp] theorem substitution_X (eta : S → Poly S) (j : Index S (Fin 4)) :
    substitution eta (X j) =
      Polynomial.C (X j) + Polynomial.C (prolong eta j.1 j.2) * Polynomial.X := by
  simp [substitution]

theorem substitution_zero (eta : S → Poly S) (p : Poly S) :
    (substitution eta p).coeff 0 = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p j hp => simp [map_mul, Polynomial.mul_coeff_zero, substitution_X, hp]

theorem substitution_first (eta : S → Poly S) (p : Poly S) :
    (substitution eta p).coeff 1 = variation eta p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.mul_coeff_one, (variation eta).leibniz]
    simp [substitution_X, substitution_zero, hp, variation_X, smul_eq_mul]
    ring

end
end Math.JetFirstVariation
