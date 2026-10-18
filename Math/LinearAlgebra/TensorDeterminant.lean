import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Basic.Complex.Basic

/-! Determinants of tensor actions, with no evaluated dimension or matrix rank. -/
namespace Math.TensorDeterminant
set_option autoImplicit false
noncomputable section
variable {A B I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

theorem map (b : Module.Basis I ℂ A) (c : Module.Basis J ℂ B)
    (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B) :
    LinearMap.det (TensorProduct.map f g) =
      LinearMap.det f ^ Fintype.card J * LinearMap.det g ^ Fintype.card I := by
  rw [← LinearMap.det_toMatrix (b.tensorProduct c), TensorProduct.toMatrix_map,
    Matrix.det_kronecker, LinearMap.det_toMatrix, LinearMap.det_toMatrix]

theorem map_one (b : Module.Basis I ℂ A) (c : Module.Basis J ℂ B)
    (f : A →ₗ[ℂ] A) (g : B →ₗ[ℂ] B)
    (hf : LinearMap.det f = 1) (hg : LinearMap.det g = 1) :
    LinearMap.det (TensorProduct.map f g) = 1 := by
  rw [map b c f g, hf, hg, one_pow, one_pow, one_mul]

end
end Math.TensorDeterminant
