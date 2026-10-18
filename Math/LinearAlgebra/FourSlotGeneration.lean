import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-! Extensionality on finite spanning families in four tensor slots. -/
set_option autoImplicit false
namespace Math.FourSlotGeneration
noncomputable section
open scoped TensorProduct
variable {k : Type*} [CommRing k]
  {I J L A B D Q U E W : Type*} [Fintype I] [Fintype J] [Fintype L]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup D] [Module k D] [AddCommGroup Q] [Module k Q]
  [AddCommGroup U] [Module k U] [AddCommGroup E] [Module k E]
  [AddCommGroup W] [Module k W]

def sumMap (f : I → A →ₗ[k] Q) : (I → A) →ₗ[k] Q :=
  ∑ i, (f i).comp (LinearMap.proj i)

theorem ext (q : I → A →ₗ[k] Q) (u : J → B →ₗ[k] U) (e : L → D →ₗ[k] E)
    (hq : Function.Surjective (sumMap q)) (hu : Function.Surjective (sumMap u))
    (he : Function.Surjective (sumMap e))
    (f g : (Q ⊗[k] Q) ⊗[k] (U ⊗[k] E) →ₗ[k] W)
    (h : ∀ i j a b x y z t,
      f ((q i x ⊗ₜ[k] q j y) ⊗ₜ[k] (u a z ⊗ₜ[k] e b t)) =
      g ((q i x ⊗ₜ[k] q j y) ⊗ₜ[k] (u a z ⊗ₜ[k] e b t))) : f = g := by
  apply TensorProduct.ext_fourfold'
  intro x y z t
  obtain ⟨x, rfl⟩ := hq x
  obtain ⟨y, rfl⟩ := hq y
  obtain ⟨z, rfl⟩ := hu z
  obtain ⟨t, rfl⟩ := he t
  simp only [sumMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, h]

end
end Math.FourSlotGeneration
