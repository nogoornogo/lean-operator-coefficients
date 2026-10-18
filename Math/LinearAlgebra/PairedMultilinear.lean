import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Basic.Complex.Basic

/-! Separate multilinearity of a multilinear map applied to paired tensor slots. -/
namespace Math.PairedMultilinear
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A B N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup N] [Module ℂ N] {n : ℕ}

def map (f : MultilinearMap ℂ (fun _ : Fin n => A ⊗[ℂ] B) N) :
    MultilinearMap ℂ (fun _ : Fin n => A)
      (MultilinearMap ℂ (fun _ : Fin n => B) N) where
  toFun a := f.compLinearMap (fun i => TensorProduct.mk ℂ A B (a i))
  map_update_add' a i x y := by
    ext w
    change f (fun j => Function.update a i (x+y) j ⊗ₜ[ℂ] w j) =
      f (fun j => Function.update a i x j ⊗ₜ[ℂ] w j) +
        f (fun j => Function.update a i y j ⊗ₜ[ℂ] w j)
    have h (z : A) : (fun j => Function.update a i z j ⊗ₜ[ℂ] w j) =
        Function.update (fun j => a j ⊗ₜ[ℂ] w j) i (z ⊗ₜ[ℂ] w i) := by
      funext j
      by_cases hj : j=i
      · subst j; simp
      · simp [hj]
    simp only [h, TensorProduct.add_tmul, f.map_update_add]
  map_update_smul' a i c x := by
    ext w
    change f (fun j => Function.update a i (c • x) j ⊗ₜ[ℂ] w j) =
      c • f (fun j => Function.update a i x j ⊗ₜ[ℂ] w j)
    have h (z : A) : (fun j => Function.update a i z j ⊗ₜ[ℂ] w j) =
        Function.update (fun j => a j ⊗ₜ[ℂ] w j) i (z ⊗ₜ[ℂ] w i) := by
      funext j
      by_cases hj : j=i
      · subst j; simp
      · simp [hj]
    simp only [h, ← TensorProduct.smul_tmul', f.map_update_smul]

@[simp] theorem apply (f : MultilinearMap ℂ (fun _ : Fin n => A ⊗[ℂ] B) N)
    (a : Fin n → A) (b : Fin n → B) :
    map f a b = f (fun i => a i ⊗ₜ[ℂ] b i) := rfl

end
end Math.PairedMultilinear
