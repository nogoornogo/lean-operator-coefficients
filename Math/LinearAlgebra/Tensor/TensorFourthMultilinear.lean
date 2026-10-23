import Math.LinearAlgebra.Tensor.TensorCubeMultilinear

/-! Four-variable multilinear maps using an associated tensor fourth power. -/
namespace Math.TensorFourthMultilinear
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {V N : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup N] [Module ℂ N]

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance

abbrev Tensor := V ⊗[ℂ] (V ⊗[ℂ] (V ⊗[ℂ] V))

def toMultilinear (f : Tensor (V := V) →ₗ[ℂ] N) :
    MultilinearMap ℂ (fun _ : Fin 4 => V) N :=
  MultilinearMap.mk' (fun v => f (v 0 ⊗ₜ[ℂ] (v 1 ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3))))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by intro v i z x; fin_cases i <;>
      simp [Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul])

def fromThree : MultilinearMap ℂ (fun _ : Fin 3 => V) N →ₗ[ℂ]
    ((V ⊗[ℂ] (V ⊗[ℂ] V)) →ₗ[ℂ] N) where
  toFun := TensorCubeMultilinear.fromMultilinear
  map_add' f g := by ext a b c; rfl
  map_smul' z f := by ext a b c; rfl

def fromMultilinear (f : MultilinearMap ℂ (fun _ : Fin 4 => V) N) :
    Tensor (V := V) →ₗ[ℂ] N :=
  TensorProduct.lift (fromThree.comp f.curryLeft)

@[simp] theorem from_pure (f : MultilinearMap ℂ (fun _ : Fin 4 => V) N) (a b c d : V) :
    fromMultilinear f (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)))=f ![a,b,c,d] := rfl

end
end Math.TensorFourthMultilinear
