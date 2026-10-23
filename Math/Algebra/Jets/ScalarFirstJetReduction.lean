import Math.RepresentationTheory.Jets.TwoSpeciesDerivativeChecks
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Free one-direction two-species first-jet reduction with actual EOM/IBP. -/
namespace Math.ScalarFirstJetReduction
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetAlgebra TwoSpeciesDerivativeChecks
abbrev P := MvPolynomial (Fin 2 × Fin 2) ℂ

def d : Derivation ℂ P P :=
  (X (0,1) : P) • pderiv (0,0)+(X (1,1) : P) • pderiv (1,0)

@[simp] theorem d_X (s k : Fin 2) : d (X (s,k)) = if k = 0 then X (s,1) else 0 := by
  fin_cases s <;> fin_cases k <;> simp [d]

def jet (j : Index (Fin 2) Unit) : P :=
  if order j.2 = 0 then X (j.1,0) else if order j.2 = 1 then X (j.1,1) else 0

def projection : A →ₐ[ℂ] P := aeval jet

@[simp] theorem projection_X (j : Index (Fin 2) Unit) : projection (X j) = jet j := by
  simp [projection]

theorem jet_shift (j : Index (Fin 2) Unit) : jet (shift () j) = d (jet j) := by
  have ho : order (shift () j).2 = order j.2+1 := by
    simp [shift,order,map_add,Finsupp.weight_single]
  by_cases h0 : order j.2 = 0
  · simp [jet,ho,h0,show (shift () j).1 = j.1 from rfl]
  · by_cases h1 : order j.2 = 1
    · simp [jet,ho,h1]
    · simp [jet,ho,h0,h1]

theorem derivative (p : A) : projection (D () p) = d (projection p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    simp only [ScalarJetAlgebra.totalDerivative_mul,map_add,map_mul,
      totalDerivative_X,projection_X,jet_shift,hp]
    exact (Derivation.leibniz d (projection p) (jet j)).symm

@[simp] theorem projection_field (s : Fin 2) : projection (field s) = X (s,0) := by
  simp [field,jet,order]
@[simp] theorem projection_first (s : Fin 2) : projection (first s) = X (s,1) := by
  rw [first,derivative,projection_field,d_X]
  simp
@[simp] theorem projection_seed (s : Fin 2) : projection (seed s) = 0 := by
  rw [seed,derivative,projection_first,d_X]
  simp

theorem equations_zero {p : A} (hp : p ∈ DifferentialEquation.ideal D equations) : projection p = 0 := by
  have hle : DifferentialEquation.ideal D equations ≤ RingHom.ker projection.toRingHom := by
    apply DifferentialEquation.minimal
    · rintro _ ⟨s,rfl⟩
      exact projection_seed s
    · intro i p hp
      cases i
      change projection (D () p) = 0
      rw [derivative,show projection p = 0 from hp,map_zero]
  exact hle hp

def exponent (a b c e : ℕ) : (Fin 2 × Fin 2) →₀ ℕ :=
  Finsupp.single (0,0) a+Finsupp.single (0,1) b+
    Finsupp.single (1,0) c+Finsupp.single (1,1) e

@[simp] theorem exponent_eq (a b c e u v w z : ℕ) :
    exponent a b c e = exponent u v w z ↔ a = u ∧ b = v ∧ c = w ∧ e = z := by
  constructor
  · intro h
    exact ⟨by simpa [exponent] using congrArg (fun p => p (0,0)) h,
      by simpa [exponent] using congrArg (fun p => p (0,1)) h,
      by simpa [exponent] using congrArg (fun p => p (1,0)) h,
      by simpa [exponent] using congrArg (fun p => p (1,1)) h⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

def coefficient (a b c e : ℕ) : P →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ (exponent a b c e)

/-- Extracting a derivative coefficient uses only the two predecessor monomials. -/
theorem coefficient_d (a b c e : ℕ) (p : P) :
    coefficient a b c e (d p) =
      (if b = 0 then 0 else (a+1 : ℂ)*coefficient (a+1) (b-1) c e p)+
      (if e = 0 then 0 else (c+1 : ℂ)*coefficient a b (c+1) (e-1) p) := by
  classical
  change ((X (0,1)*pderiv (0,0) p+X (1,1)*pderiv (1,0) p) : P).coeff _ = _
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  rw [coeff_X_mul',coeff_X_mul']
  have h0 : exponent a b c e (0,1) = b := by simp [exponent]
  have h1 : exponent a b c e (1,1) = e := by simp [exponent]
  simp only [Finsupp.mem_support_iff,h0,h1]
  have he0 : exponent a b c e-Finsupp.single (0,1) 1 = exponent a (b-1) c e := by
    ext ⟨s,k⟩
    fin_cases s <;> fin_cases k <;> simp [exponent]
  have he1 : exponent a b c e-Finsupp.single (1,1) 1 = exponent a b c (e-1) := by
    ext ⟨s,k⟩
    fin_cases s <;> fin_cases k <;> simp [exponent]
  have ha0 : exponent a (b-1) c e+Finsupp.single (0,0) 1 = exponent (a+1) (b-1) c e := by
    ext ⟨s,k⟩
    fin_cases s <;> fin_cases k <;> simp [exponent]
  have ha1 : exponent a b c (e-1)+Finsupp.single (1,0) 1 = exponent a b (c+1) (e-1) := by
    ext ⟨s,k⟩
    fin_cases s <;> fin_cases k <;> simp [exponent]
  simp only [he0,he1,coeff_pderiv,ha0,ha1]
  have he00 : exponent a (b-1) c e (0,0) = a := by simp [exponent]
  have he11 : exponent a b c (e-1) (1,0) = c := by simp [exponent]
  simp only [he00,he11]
  split_ifs <;> simp_all [coefficient,mul_comm]

def firstFunctional (r : ℕ) : P →ₗ[ℂ] ℂ :=
  coefficient r 1 (r+1) 0-coefficient (r+1) 0 r 1

def secondFunctional : P →ₗ[ℂ] ℂ :=
  (-2 : ℂ) • coefficient 0 2 2 0+coefficient 1 1 1 1+(-2 : ℂ) • coefficient 2 0 0 2

theorem first_derivative (r : ℕ) (p : P) : firstFunctional r (d p) = 0 := by
  simp [firstFunctional,coefficient_d]

theorem second_derivative (p : P) : secondFunctional (d p) = 0 := by
  simp [secondFunctional,coefficient_d]
  ring

def onJets (f : P →ₗ[ℂ] ℂ) : A →ₗ[ℂ] ℂ := f.comp projection.toLinearMap

theorem annihilates (f : P →ₗ[ℂ] ℂ) (hf : ∀ p, f (d p) = 0) : T ≤ (onJets f).ker := by
  apply sup_le
  · intro p hp
    change f (projection p) = 0
    rw [equations_zero hp,map_zero]
  · rintro _ ⟨v,rfl⟩
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simpa only [map_add] using (onJets f).ker.add_mem hv hw
    | single i p =>
      cases i
      rw [DifferentialEquation.divergence_single]
      change f (projection (D () p)) = 0
      rw [derivative,hf]
end
end Math.ScalarFirstJetReduction
