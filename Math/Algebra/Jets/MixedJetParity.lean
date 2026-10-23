import Math.Algebra.Jets.MixedJetAlgebra
import Math.LinearAlgebra.Exterior.ExteriorOdd

/-! Parity and generator sliding in the actual mixed jet algebra. -/
namespace Math.MixedJetParity
set_option autoImplicit false
noncomputable section
open MixedJetAlgebra
open scoped TensorProduct
variable {F B I : Type*}

def involute : Algebra F B I →ₐ[ℂ] Algebra F B I :=
  Algebra.TensorProduct.map CliffordAlgebra.involute (AlgHom.id ℂ _)

@[simp] theorem involute_tmul (x : Odd F I) (y : Even B I) :
    involute (x ⊗ₜ[ℂ] y) = CliffordAlgebra.involute x ⊗ₜ[ℂ] y := rfl

@[simp] theorem involute_odd (j : ScalarJetAlgebra.Index F I) :
    involute (odd (B := B) j) = -odd j := by
  simp [odd, involute, Algebra.TensorProduct.map_tmul]
  rfl

@[simp] theorem involute_even (j : ScalarJetAlgebra.Index B I) :
    involute (even (F := F) j) = even j := by
  simp [even, involute, Algebra.TensorProduct.map_tmul]

theorem involute_derivative (i : I) (p : Algebra F B I) :
    involute (totalDerivative i p) = totalDerivative i (involute p) := by
  have h (x : Odd F I) : CliffordAlgebra.involute (oddDerivative i x) =
      oddDerivative i (CliffordAlgebra.involute x) := by
    exact ExteriorAlgebra.algHom_derivationOfLinear CliffordAlgebra.involute
      (f := -LinearMap.id) (by intro v; simp) (by intro v; simp) x
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul x y => simp only [totalDerivative_tmul, map_add, involute_tmul, h]

theorem odd_slide (j : ScalarJetAlgebra.Index F I) (p : Algebra F B I) :
    odd j * p = involute p * odd j := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [mul_add, map_add, add_mul, hp, hq]
  | tmul x y =>
    simp only [odd, Algebra.TensorProduct.tmul_mul_tmul, involute_tmul, one_mul, mul_one]
    rw [ExteriorOdd.generator_slide]

theorem even_central (j : ScalarJetAlgebra.Index B I) (p : Algebra F B I) :
    even j * p = p * even j := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [mul_add, add_mul, hp, hq]
  | tmul x y =>
    simp only [even, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [mul_comm (MvPolynomial.X j) y]

end
end Math.MixedJetParity
