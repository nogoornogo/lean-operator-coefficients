import Math.Algebra.Variational.LocalEuler
import Math.LinearAlgebra.Exterior.ExteriorLeftDerivative
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Actual left jet derivatives. Odd coordinates use Clifford contraction;
even coordinates use polynomial differentiation. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {F B I : Type*}
local instance partialDecF : DecidableEq F := Classical.decEq _
local instance partialDecB : DecidableEq B := Classical.decEq _
local instance partialDecI : DecidableEq I := Classical.decEq _
@[reducible] local instance partialAdd : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance partialModule : Module ℂ (A F B I) := inferInstance
@[reducible] local instance partialRing : Ring (A F B I) := inferInstance

/-- Left derivative with respect to one actual, commuting-multiindex jet. -/
def jetPartial (s : Field F B) (a : I →₀ ℕ) : A F B I →ₗ[ℂ] A F B I :=
  match s with
  | .inl f => TensorProduct.map
      (Math.ExteriorLeftDerivative.derivative (Finsupp.lapply (f,a))) LinearMap.id
  | .inr b => TensorProduct.map LinearMap.id (MvPolynomial.pderiv (b,a)).toLinearMap

@[simp] theorem partial_odd_tmul (f : F) (a : I →₀ ℕ)
    (x : MixedJetAlgebra.Odd F I) (y : MixedJetAlgebra.Even B I) :
    jetPartial (.inl f) a (x ⊗ₜ[ℂ] y) =
      Math.ExteriorLeftDerivative.derivative (Finsupp.lapply (f,a)) x ⊗ₜ[ℂ] y := rfl

@[simp] theorem partial_even_tmul (b : B) (a : I →₀ ℕ)
    (x : MixedJetAlgebra.Odd F I) (y : MixedJetAlgebra.Even B I) :
    jetPartial (.inr b) a (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] MvPolynomial.pderiv (b,a) y := rfl

@[simp] theorem partial_constant (s : Field F B) (a : I →₀ ℕ) (c : ℂ) :
    jetPartial s a (algebraMap ℂ (A F B I) c) = 0 := by
  cases s <;> simp [jetPartial, Algebra.TensorProduct.algebraMap_def,
    Math.ExteriorLeftDerivative.derivative]

@[simp] theorem partial_odd (s : Field F B) (a : I →₀ ℕ) (f : F) (b : I →₀ ℕ) :
    jetPartial s a (MixedJetAlgebra.odd (B := B) (f,b)) =
      if s = .inl f ∧ a = b then 1 else 0 := by
  classical
  cases s <;> simp [MixedJetAlgebra.odd, jetPartial,
    Math.ExteriorLeftDerivative.derivative, Finsupp.single_apply,
    Algebra.TensorProduct.one_def, eq_comm]
  split_ifs <;> simp_all

@[simp] theorem partial_even (s : Field F B) (a : I →₀ ℕ) (b : B) (v : I →₀ ℕ) :
    jetPartial s a (MixedJetAlgebra.even (F := F) (b,v)) =
      if s = .inr b ∧ a = v then 1 else 0 := by
  classical
  cases s <;> simp [MixedJetAlgebra.even, jetPartial,
    Math.ExteriorLeftDerivative.derivative, MvPolynomial.pderiv_X,
    Algebra.TensorProduct.one_def, eq_comm, Pi.single_apply]
  split_ifs <;> simp_all

theorem partial_mul (s : Field F B) (a : I →₀ ℕ) (p q : A F B I) :
    jetPartial s a (p*q) = jetPartial s a p*q + twist s p*jetPartial s a q := by
  induction p using TensorProduct.inductionOn with
  | add p r hp hr => cases s <;> simp_all [twist, add_mul] <;> abel
  | tmul x y =>
    induction q using TensorProduct.inductionOn with
    | add q r hq hr => cases s <;> simp_all [twist, mul_add] <;> abel
    | tmul z w =>
      cases s with
      | inl f => simp [Algebra.TensorProduct.tmul_mul_tmul,
          Math.ExteriorLeftDerivative.leibniz, twist, TensorProduct.add_tmul]
      | inr b =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, partial_even_tmul,
          MvPolynomial.pderiv_mul, TensorProduct.tmul_add, twist]


end
end Math.LocalPolynomial
