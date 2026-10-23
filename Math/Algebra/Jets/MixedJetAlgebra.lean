import Math.Algebra.Jets.JetLinear
import PhyslibAlpha.Mathematics.ExteriorAlgebra
import Mathlib.RingTheory.TensorProduct.Basic

/-! The actual unbounded exterior/polynomial mixed jet algebra.
The spacetime derivative is even, including on products of two odd fields. -/
namespace Math.MixedJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear
open scoped TensorProduct

abbrev Odd (S I : Type*) := ExteriorAlgebra ℂ (Jet S I)
abbrev Even (S I : Type*) := ScalarJetAlgebra.Algebra S I
abbrev Algebra (F B I : Type*) := Odd F I ⊗[ℂ] Even B I

variable {F B I : Type*}

def oddDerivative (i : I) : Odd F I →ₗ[ℂ] Odd F I :=
  ExteriorAlgebra.derivationOfLinear (JetLinear.shift i)

def totalDerivative (i : I) : Algebra F B I →ₗ[ℂ] Algebra F B I :=
  TensorProduct.map (oddDerivative i) LinearMap.id +
    TensorProduct.map LinearMap.id (ScalarJetAlgebra.totalDerivative i).toLinearMap

@[simp] theorem totalDerivative_tmul (i : I) (x : Odd F I) (y : Even B I) :
    totalDerivative i (x ⊗ₜ[ℂ] y) =
      oddDerivative i x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] ScalarJetAlgebra.totalDerivative i y := by
  simp [totalDerivative]

@[simp] theorem totalDerivative_one (i : I) : totalDerivative i (1 : Algebra F B I) = 0 := by
  rw [Algebra.TensorProduct.one_def, totalDerivative_tmul]
  simp [oddDerivative]

theorem totalDerivative_mul (i : I) (p q : Algebra F B I) :
    totalDerivative i (p * q) = totalDerivative i p * q + p * totalDerivative i q := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]; abel
  | tmul x y =>
    induction q using TensorProduct.inductionOn with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]; abel
    | tmul z w =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, totalDerivative_tmul, oddDerivative,
        ExteriorAlgebra.derivationOfLinear_mul, ScalarJetAlgebra.totalDerivative_mul,
        TensorProduct.add_tmul, TensorProduct.tmul_add, add_mul, mul_add]
      rw [mul_comm y (ScalarJetAlgebra.totalDerivative i w),
        mul_comm w (ScalarJetAlgebra.totalDerivative i y)]
      abel

theorem totalDerivative_commute (i j : I) (p : Algebra F B I) :
    totalDerivative i (totalDerivative j p) = totalDerivative j (totalDerivative i p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul x y =>
    simp only [totalDerivative_tmul, map_add, oddDerivative,
      ExteriorAlgebra.derivationOfLinear_comm_apply (JetLinear.shift_commute i j),
      ScalarJetAlgebra.totalDerivative_commute i j]
    abel

def odd (j : ScalarJetAlgebra.Index F I) : Algebra F B I :=
  (ExteriorAlgebra.ι ℂ : Jet F I →ₗ[ℂ] Odd F I) (Finsupp.single j 1) ⊗ₜ[ℂ] (1 : Even B I)

def even (j : ScalarJetAlgebra.Index B I) : Algebra F B I :=
  (1 : Odd F I) ⊗ₜ[ℂ] MvPolynomial.X j

@[simp] theorem totalDerivative_odd (i : I) (j : ScalarJetAlgebra.Index F I) :
    totalDerivative i (odd (B := B) j) = odd (ScalarJetAlgebra.shift i j) := by
  simp [odd, oddDerivative]

@[simp] theorem totalDerivative_even (i : I) (j : ScalarJetAlgebra.Index B I) :
    totalDerivative i (even (F := F) j) = even (ScalarJetAlgebra.shift i j) := by
  simp [even, oddDerivative]

theorem odd_square (j : ScalarJetAlgebra.Index F I) : (odd (B := B) j) ^ 2 = 0 := by
  simp [odd, pow_two, Algebra.TensorProduct.tmul_mul_tmul]

def action {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) : Representation ℂ H (Algebra F B I) :=
  (Representation.exteriorAlgebra (JetLinear.action ρF)).tprod (polynomialAction ρB)

theorem odd_covariance {H : Type*} [Group H] (ρ : Representation ℂ H (JetLinear.Field F))
    (h : H) (i : I) (x : Odd F I) :
    Representation.exteriorAlgebra (JetLinear.action ρ) h (oddDerivative i x) =
      oddDerivative i (Representation.exteriorAlgebra (JetLinear.action ρ) h x) := by
  exact ExteriorAlgebra.algHom_derivationOfLinear
    (ExteriorAlgebra.map (JetLinear.map (ρ h)))
    (fun _ => ExteriorAlgebra.map_apply_ι _ _) (fun v => map_shift (ρ h) i v) x

theorem covariance {H : Type*} [Group H] (ρF : Representation ℂ H (JetLinear.Field F))
    (ρB : Representation ℂ H (JetLinear.Field B)) (h : H) (i : I) (p : Algebra F B I) :
    action ρF ρB h (totalDerivative i p) = totalDerivative i (action ρF ρB h p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul x y =>
    simp only [totalDerivative_tmul, map_add, action, Representation.tprod_apply,
      TensorProduct.map_tmul]
    rw [odd_covariance]
    change _ = _ + _ ⊗ₜ[ℂ] ScalarJetAlgebra.totalDerivative i (polynomialMap (ρB h) y)
    rw [derivative_polynomialMap]
    rfl

end
end Math.MixedJetAlgebra
