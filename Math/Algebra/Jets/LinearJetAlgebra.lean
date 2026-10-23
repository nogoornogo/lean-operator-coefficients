import Math.Algebra.Jets.LinearJetEquation
import Math.Algebra.Jets.MixedJetAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Actual free odd/even algebras on linear-equation quotient generators. -/
namespace Math.LinearJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear JetDirections LinearJetEquation
open scoped TensorProduct

variable {F B I EF EB : Type*} [AddCommGroup EF] [Module ℂ EF]
  [AddCommGroup EB] [Module ℂ EB]
  (eF : EF →ₗ[ℂ] Jet F I) (eB : EB →ₗ[ℂ] Jet B I)

abbrev Odd := ExteriorAlgebra ℂ (Generator eF)
abbrev Even := SymmetricAlgebra ℂ (Generator eB)
abbrev Algebra := Odd eF ⊗[ℂ] Even eB

def oddProjection : MixedJetAlgebra.Odd F I →ₐ[ℂ] Odd eF := ExteriorAlgebra.map (relations eF).mkQ

def evenProjection : MixedJetAlgebra.Even B I →ₐ[ℂ] Even eB :=
  MvPolynomial.aeval (fun j => SymmetricAlgebra.ι ℂ (Generator eB)
    ((relations eB).mkQ (Finsupp.single j 1)))

@[simp] theorem oddProjection_ι (v : Jet F I) :
    oddProjection eF (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ ((relations eF).mkQ v) :=
  ExteriorAlgebra.map_apply_ι _ _

@[simp] theorem evenProjection_X (j : ScalarJetAlgebra.Index B I) :
    evenProjection eB (MvPolynomial.X j) = SymmetricAlgebra.ι ℂ (Generator eB)
      ((relations eB).mkQ (Finsupp.single j 1)) := by simp [evenProjection]

theorem evenProjection_linearForm (v : Jet B I) :
    evenProjection eB (JetLinear.linearForm v) = SymmetricAlgebra.ι ℂ (Generator eB) ((relations eB).mkQ v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single j c =>
    simp only [show Finsupp.single j c = c • Finsupp.single j (1 : ℂ) by simp,
      map_smul, JetLinear.linearForm, Finsupp.linearCombination_single, one_smul, evenProjection_X]

theorem oddProjection_surjective : Function.Surjective (oddProjection eF) :=
  ExteriorAlgebra.map_surjective_iff.mpr (relations eF).mkQ_surjective

theorem evenProjection_surjective : Function.Surjective (evenProjection eB) := by
  intro x
  induction x using SymmetricAlgebra.induction with
  | algebraMap c => exact ⟨MvPolynomial.C c, (evenProjection eB).commutes c⟩
  | ι v =>
    obtain ⟨v, rfl⟩ := (relations eB).mkQ_surjective v
    exact ⟨JetLinear.linearForm v, evenProjection_linearForm eB v⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩
  | mul x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
    exact ⟨x * y, map_mul _ _ _⟩

def projection : MixedJetAlgebra.Algebra F B I →ₐ[ℂ] Algebra eF eB :=
  Algebra.TensorProduct.map (oddProjection eF) (evenProjection eB)

@[simp] theorem projection_tmul (x : MixedJetAlgebra.Odd F I) (y : MixedJetAlgebra.Even B I) :
    projection eF eB (x ⊗ₜ[ℂ] y) = oddProjection eF x ⊗ₜ[ℂ] evenProjection eB y := rfl

theorem projection_surjective : Function.Surjective (projection eF eB) :=
  Algebra.TensorProduct.map_surjective (oddProjection eF) (evenProjection eB)
    (oddProjection_surjective eF) (evenProjection_surjective eB)

def oddDerivative (i : I) : Odd eF →ₗ[ℂ] Odd eF := ExteriorAlgebra.derivationOfLinear (shift eF i)
def evenDerivative (i : I) : Even eB →ₗ[ℂ] Even eB :=
  PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear (shift eB i)

def derivative (i : I) : Algebra eF eB →ₗ[ℂ] Algebra eF eB :=
  TensorProduct.map (oddDerivative eF i) LinearMap.id + TensorProduct.map LinearMap.id (evenDerivative eB i)

@[simp] theorem derivative_tmul (i : I) (x : Odd eF) (y : Even eB) :
    derivative eF eB i (x ⊗ₜ[ℂ] y) = oddDerivative eF i x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] evenDerivative eB i y := by
  simp [derivative]

theorem derivative_mul (i : I) (p q : Algebra eF eB) :
    derivative eF eB i (p * q) = derivative eF eB i p * q + p * derivative eF eB i q := by
  induction p using TensorProduct.inductionOn with
  | add x z hx hz => simp only [add_mul, map_add, hx, hz]; abel
  | tmul x y =>
    induction q using TensorProduct.inductionOn with
    | add z w hz hw => simp only [mul_add, map_add, hz, hw]; abel
    | tmul z w =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, derivative_tmul, oddDerivative, evenDerivative,
        ExteriorAlgebra.derivationOfLinear_mul, PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_mul,
        TensorProduct.add_tmul, TensorProduct.tmul_add, add_mul, mul_add]
      abel

theorem derivative_commute (i j : I) (x : Algebra eF eB) :
    derivative eF eB i (derivative eF eB j x) = derivative eF eB j (derivative eF eB i x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [derivative_tmul, map_add, oddDerivative, evenDerivative,
      ExteriorAlgebra.derivationOfLinear_comm_apply (shift_commute eF i j),
      PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_comm_apply (shift_commute eB i j)]
    abel

theorem oddProjection_derivative (i : I) (x : MixedJetAlgebra.Odd F I) :
    oddProjection eF (MixedJetAlgebra.oddDerivative i x) = oddDerivative eF i (oddProjection eF x) :=
  ExteriorAlgebra.algHom_derivationOfLinear (oddProjection eF) (oddProjection_ι eF)
    (fun v => (shift_mk eF i v).symm) x

theorem evenProjection_derivative (i : I) (x : MixedJetAlgebra.Even B I) :
    evenProjection eB (ScalarJetAlgebra.totalDerivative i x) = evenDerivative eB i (evenProjection eB x) := by
  induction x using MvPolynomial.induction_on with
  | C c => simp [evenProjection, evenDerivative]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X x j hx =>
    simp only [ScalarJetAlgebra.totalDerivative_mul, map_add, map_mul, hx,
      ScalarJetAlgebra.totalDerivative_X, evenProjection_X, evenDerivative,
      PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_mul,
      PhyslibSymmetric.SymmetricAlgebra.derivationOfLinear_ι, shift_mk, JetLinear.shift_single]
    ring

theorem projection_derivative (i : I) (x : MixedJetAlgebra.Algebra F B I) :
    projection eF eB (MixedJetAlgebra.totalDerivative i x) = derivative eF eB i (projection eF eB x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [MixedJetAlgebra.totalDerivative_tmul, map_add, projection_tmul, derivative_tmul,
      oddProjection_derivative, evenProjection_derivative]

end
end Math.LinearJetAlgebra
