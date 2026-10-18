import Math.LinearAlgebra.ExteriorFourthKernels
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.SymmetricPower.Basis

/-! The symbolic quartic exhaustion identity in an arbitrary dimension.
This does not assert embeddings of the three proposed branches. -/
namespace Math.ExteriorFourthDimensions
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open ExteriorFourthKernels

theorem binomial_identity (n k l : ℕ)
    (hk : n * n.choose 3=n.choose 4+k)
    (hl : (n.choose 2).multichoose 2=n.choose 4+l) :
    5*n.choose 4+3*k+l=(2*n).choose 4 := by
  have h2 := Nat.descFactorial_eq_factorial_mul_choose n 2
  have h3 := Nat.descFactorial_eq_factorial_mul_choose n 3
  have h4 := Nat.descFactorial_eq_factorial_mul_choose n 4
  have ht := Nat.descFactorial_eq_factorial_mul_choose (2*n) 4
  have hs := Nat.descFactorial_eq_factorial_mul_choose (n.choose 2+1) 2
  rw [Nat.multichoose_eq] at hl
  have hshift : n.choose 2+2-1=n.choose 2+1 := by omega
  rw [hshift] at hl
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.mul_one,
    Nat.factorial_succ, Nat.factorial_zero] at h2 h3 h4 ht hs
  rcases n with _ | _ | _ | n
  · norm_num [Nat.choose, Nat.multichoose] at hk hl ⊢
    omega
  · norm_num [Nat.choose, Nat.multichoose] at hk hl ⊢
    omega
  · norm_num [Nat.choose, Nat.multichoose] at hk hl ⊢
    omega
  · have e1 : n+1+1+1-1=n+2 := by omega
    have e2 : n+1+1+1-2=n+1 := by omega
    have e3 : n+1+1+1-3=n := by omega
    have e4 : 2*(n+1+1+1)-1=2*n+5 := by omega
    have e5 : 2*(n+1+1+1)-2=2*n+4 := by omega
    have e6 : 2*(n+1+1+1)-3=2*n+3 := by omega
    simp only [Nat.sub_zero, Nat.add_sub_cancel, e1, e2, e3, e4, e5, e6] at h2 h3 h4 ht hs
    qify at hk hl h2 h3 h4 ht hs ⊢
    rw [hl] at hs
    have h3n := congrArg (fun x : ℚ => (n+1+1+1)*x) h3
    have h2sq := congrArg (fun x : ℚ => x*x) h2
    linear_combination -3*hk - (1/2 : ℚ)*hs - (1/24 : ℚ)*h4 -
      (1/2 : ℚ)*h3n - (1/8 : ℚ)*h2sq - (1/4 : ℚ)*h2 + (1/24 : ℚ)*ht

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {A : Type*} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
@[reducible] local instance : AddCommGroup (Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem kernel211_dimension :
    Module.finrank ℂ A * (Module.finrank ℂ A).choose 3 =
      (Module.finrank ℂ A).choose 4+Module.finrank ℂ (K211 (A := A)) := by
  have h := (split13 (A := A)).finrank_eq
  simpa only [Module.finrank_tensorProduct, Module.finrank_prod,
    exteriorPower.finrank_eq] using h

theorem kernel22_dimension :
    ((Module.finrank ℂ A).choose 2).multichoose 2 =
      (Module.finrank ℂ A).choose 4+Module.finrank ℂ (K22 (A := A)) := by
  have h := (split22 (A := A)).finrank_eq
  simpa only [SymmetricPower.finrank_eq, Module.finrank_prod,
    exteriorPower.finrank_eq] using h

/-- Exhaustion reduces to independence and construction of the actual maps;
no content-specific dimension or multiplicity is evaluated. -/
theorem dimension_balance :
    5*(Module.finrank ℂ A).choose 4+3*Module.finrank ℂ (K211 (A := A))+
      Module.finrank ℂ (K22 (A := A))=(2*Module.finrank ℂ A).choose 4 :=
  binomial_identity _ _ _ kernel211_dimension kernel22_dimension

variable {B : Type*} [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]

abbrev Candidate := ((⋀[ℂ]^4 A) ⊗[ℂ] Sym[ℂ]^4 B) ×
  (K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) × K22 (A := A)

@[reducible] local instance : AddCommGroup (Candidate (A := A) (B := B)) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem candidate_dimensions (hb : Module.finrank ℂ B=2) :
    Module.finrank ℂ (Candidate (A := A) (B := B))=
      Module.finrank ℂ (⋀[ℂ]^4 (A ⊗[ℂ] B)) := by
  change Module.finrank ℂ (((⋀[ℂ]^4 A) ⊗[ℂ] Sym[ℂ]^4 B) ×
    (K211 (A := A) ⊗[ℂ] Sym[ℂ]^2 B) × K22 (A := A))=_
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_tensorProduct,
    Module.finrank_tensorProduct, exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    SymmetricPower.finrank_eq, SymmetricPower.finrank_eq, Module.finrank_tensorProduct, hb]
  norm_num [Nat.multichoose]
  simpa only [Nat.mul_comm, Nat.add_assoc] using dimension_balance (A := A)

/-- The actual embeddings and their independence remain required. Once
provided, exhaustion follows from the proved symbolic dimension identity. -/
theorem surjective_of_injective (hb : Module.finrank ℂ B=2)
    (f : Candidate (A := A) (B := B) →ₗ[ℂ] ⋀[ℂ]^4 (A ⊗[ℂ] B))
    (hf : Function.Injective f) : Function.Surjective f :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f)
    (candidate_dimensions (A := A) (B := B) hb)).mp hf

end
end Math.ExteriorFourthDimensions
