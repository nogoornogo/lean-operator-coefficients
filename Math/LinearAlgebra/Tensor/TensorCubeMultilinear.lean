import Math.RepresentationTheory.Tensors.TensorSquareMultilinear
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Binary-associated third tensor powers and three-variable multilinear
maps, with explicit pure-tensor formulas. -/
namespace Math.TensorCubeMultilinear
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {V N : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup N] [Module ℂ N]

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

def toMultilinear (f : (V ⊗[ℂ] (V ⊗[ℂ] V)) →ₗ[ℂ] N) :
    MultilinearMap ℂ (fun _ : Fin 3 => V) N :=
  MultilinearMap.mk' (fun v => f (v 0 ⊗ₜ[ℂ] (v 1 ⊗ₜ[ℂ] v 2)))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update,TensorProduct.add_tmul,TensorProduct.tmul_add])
    (by intro v i z x; fin_cases i <;>
      simp [Function.update,TensorProduct.smul_tmul,TensorProduct.tmul_smul])

def fromMultilinear (f : MultilinearMap ℂ (fun _ : Fin 3 => V) N) :
    (V ⊗[ℂ] (V ⊗[ℂ] V)) →ₗ[ℂ] N :=
  TensorProduct.lift (TensorSquareMultilinear.equiv.symm.toLinearMap.comp f.curryLeft)

@[simp] theorem from_pure (f : MultilinearMap ℂ (fun _ : Fin 3 => V) N) (a b c : V) :
    fromMultilinear f (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c))=f ![a,b,c] := rfl

end
end Math.TensorCubeMultilinear
