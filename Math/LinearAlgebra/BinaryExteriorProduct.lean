import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.RingTheory.Flat.Basic

/-! The binary multidegree injection supplied by the graded exterior product. -/
namespace Math.BinaryExteriorProduct
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

theorem ext {P : Type*} [AddCommGroup P] [Module K P] {n m : ℕ}
    {f g : (⋀[K]^n M) ⊗[K] (⋀[K]^m N) →ₗ[K] P}
    (h : ∀ v w, f ((exteriorPower.ιMulti K n v) ⊗ₜ[K] (exteriorPower.ιMulti K m w)) =
      g ((exteriorPower.ιMulti K n v) ⊗ₜ[K] (exteriorPower.ιMulti K m w))) : f = g := by
  apply TensorProduct.ext'
  intro x y
  have hx : f.comp ((TensorProduct.mk K (⋀[K]^n M) (⋀[K]^m N)).flip y) =
      g.comp ((TensorProduct.mk K (⋀[K]^n M) (⋀[K]^m N)).flip y) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hy : f.comp (TensorProduct.mk K (⋀[K]^n M) (⋀[K]^m N) (exteriorPower.ιMulti K n v)) =
        g.comp (TensorProduct.mk K (⋀[K]^n M) (⋀[K]^m N) (exteriorPower.ιMulti K n v)) := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro w
      exact h v w
    exact LinearMap.congr_fun hy y
  exact LinearMap.congr_fun hx x

def map (n m : ℕ) : (⋀[K]^n M) ⊗[K] (⋀[K]^m N) →ₗ[K] ⋀[K]^(n+m) (M × N) :=
  TensorProduct.lift ((exteriorPower.wedge K (M × N) n m).compl₁₂
    (exteriorPower.map n (LinearMap.inl K M N))
    (exteriorPower.map m (LinearMap.inr K M N)))

theorem coe_map_tmul (n m : ℕ) (x : ⋀[K]^n M) (y : ⋀[K]^m N) :
    (map n m (x ⊗ₜ[K] y)).val =
      (ExteriorAlgebra.prodEquivTensor K M N).symm
        (x.val ᵍ⊗ₜ[K] y.val) := by
  rw [ExteriorAlgebra.prodEquivTensor_symm_tmul]
  simp [map, exteriorPower.wedge, exteriorPower.coe_map]

theorem injective (n m : ℕ) : Function.Injective (map (K := K) (M := M) (N := N) n m) := by
  let j := TensorProduct.map (Submodule.subtype (⋀[K]^n M)) (Submodule.subtype (⋀[K]^m N))
  have hj : Function.Injective j := TensorProduct.map_injective_of_flat_flat _ _
    (Submodule.injective_subtype _) (Submodule.injective_subtype _)
  have he : (Submodule.subtype (⋀[K]^(n+m) (M × N))).comp (map n m) =
      (ExteriorAlgebra.prodEquivTensor K M N).symm.toLinearMap.comp
        ((GradedTensorProduct.of K (fun i => ⋀[K]^i M) (fun i => ⋀[K]^i N)).toLinearMap.comp j) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact coe_map_tmul n m x y
  intro x y h
  apply hj
  apply (GradedTensorProduct.of K (fun i => ⋀[K]^i M) (fun i => ⋀[K]^i N)).injective
  apply (ExteriorAlgebra.prodEquivTensor K M N).symm.injective
  exact (LinearMap.congr_fun he x).symm.trans
    ((congrArg Subtype.val h).trans (LinearMap.congr_fun he y))

theorem map_pure (n m : ℕ) (v : Fin n → M) (w : Fin m → N) :
    map n m ((exteriorPower.ιMulti K n v) ⊗ₜ[K] (exteriorPower.ιMulti K m w)) =
      exteriorPower.ιMulti K (n+m)
        (Fin.append (LinearMap.inl K M N ∘ v) (LinearMap.inr K M N ∘ w)) := by
  apply Subtype.ext
  rw [coe_map_tmul]
  exact ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti K M N n m v w

end
end Math.BinaryExteriorProduct
