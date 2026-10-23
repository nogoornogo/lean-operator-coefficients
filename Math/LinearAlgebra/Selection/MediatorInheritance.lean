import Math.LinearAlgebra.Selection.MediatorExchange
import Mathlib.LinearAlgebra.Prod

/-! Support criteria for inheritance of exchange. Inverse-mass compatibility
is derived from forward compatibility; nonzero total exchange is not assumed. -/
set_option autoImplicit false
namespace Math.MediatorInheritance
noncomputable section
open scoped TensorProduct
open MediatorExchange

variable {k V W : Type*} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem inverse_intertwines (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W) (i : V →ₗ[k] W)
    (h : ∀ x, N (i x) = i (M x)) (x : V) : N.symm (i x) = i (M.symm x) := by
  apply N.injective
  rw [N.apply_symm_apply, h, M.apply_symm_apply]

theorem pairing_of_source_support (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W)
    (i : V →ₗ[k] W) (hM : ∀ x, N (i x) = i (M x))
    (J : V) (K : Module.Dual k V) (L : W) (R : Module.Dual k W)
    (hJ : L = i J) (hK : ∀ x, R (i x) = K x) :
    R (N.symm L) = K (M.symm J) := by
  rw [hJ, inverse_intertwines M N i hM, hK]

theorem pairing_of_observer_support (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W)
    (p : W →ₗ[k] V) (hM : ∀ x, p (N x) = M (p x))
    (J : V) (K : Module.Dual k V) (L : W) (R : Module.Dual k W)
    (hJ : p L = J) (hK : ∀ x, R x = K (p x)) :
    R (N.symm L) = K (M.symm J) := by
  rw [hK, ← inverse_intertwines N M p (fun x => (hM x).symm), hJ]

variable {A B C D : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]

theorem coefficient_of_source_support (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W)
    (i : V →ₗ[k] W) (g : k) (hM : ∀ x, N (i x) = i (M x))
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (L : A ⊗[k] C →ₗ[k] W) (R : B ⊗[k] D →ₗ[k] Module.Dual k W)
    (hJ : ∀ x, L x = i (J x)) (hK : ∀ y x, R y (i x) = K y x) :
    coefficient N g L R = coefficient M g J K := by
  apply TensorProduct.ext_fourfold'
  intro a b c d
  simp only [coefficient_tmul]
  rw [pairing_of_source_support M N i hM _ _ _ _ (hJ _) (hK _)]

theorem coefficient_of_observer_support (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W)
    (p : W →ₗ[k] V) (g : k) (hM : ∀ x, p (N x) = M (p x))
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (L : A ⊗[k] C →ₗ[k] W) (R : B ⊗[k] D →ₗ[k] Module.Dual k W)
    (hJ : ∀ x, p (L x) = J x) (hK : ∀ y x, R y x = K y (p x)) :
    coefficient N g L R = coefficient M g J K := by
  apply TensorProduct.ext_fourfold'
  intro a b c d
  simp only [coefficient_tmul]
  rw [pairing_of_observer_support M N p hM _ _ _ _ (hJ _) (hK _)]

variable {X : Type*} [AddCommGroup X] [Module k X]

def sumDual (K : X →ₗ[k] Module.Dual k V) (R : X →ₗ[k] Module.Dual k W) :
    X →ₗ[k] Module.Dual k (V × W) where
  toFun x := (K x).comp (LinearMap.fst k V W) + (R x).comp (LinearMap.snd k V W)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    simp [smul_add]

theorem sumDual_apply (K : X →ₗ[k] Module.Dual k V) (R : X →ₗ[k] Module.Dual k W)
    (x : X) (z : V × W) : sumDual K R x z = K x z.1 + R x z.2 := rfl

theorem product_retains_core {Y : Type*} [AddCommGroup Y] [Module k Y]
    (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W)
    (J : X →ₗ[k] V) (L : X →ₗ[k] W)
    (K : Y →ₗ[k] Module.Dual k V) (R : Y →ₗ[k] Module.Dual k W) :
    (∀ x, (M.prodCongr N) (x, 0) = (M x, 0)) ∧
    (∀ y, (J.prod L y).1 = J y) ∧
    (∀ y x, sumDual K R y (x, 0) = K y x) := by
  simp [sumDual_apply]

theorem coefficient_product (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (L : A ⊗[k] C →ₗ[k] W) (R : B ⊗[k] D →ₗ[k] Module.Dual k W) :
    coefficient (M.prodCongr N) g (J.prod L) (sumDual K R) =
      coefficient M g J K + coefficient N g L R := by
  apply TensorProduct.ext_fourfold'
  intro a b c d
  simp [coefficient_tmul, sumDual_apply, mul_add]

theorem spectator_observer_zero (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (L : A ⊗[k] C →ₗ[k] W) :
    coefficient (M.prodCongr N) g (J.prod L) (sumDual K 0) = coefficient M g J K := by
  rw [coefficient_product]
  have hz : coefficient N g L (0 : B ⊗[k] D →ₗ[k] Module.Dual k W) = 0 := by
    apply TensorProduct.ext_fourfold'
    intro a b c d
    simp [coefficient_tmul]
  rw [hz, add_zero]

theorem spectator_source_zero (M : V ≃ₗ[k] V) (N : W ≃ₗ[k] W) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (R : B ⊗[k] D →ₗ[k] Module.Dual k W) :
    coefficient (M.prodCongr N) g (J.prod (0 : A ⊗[k] C →ₗ[k] W)) (sumDual K R) =
      coefficient M g J K := by
  rw [coefficient_product]
  have hz : coefficient N g (0 : A ⊗[k] C →ₗ[k] W) R = 0 := by
    apply TensorProduct.ext_fourfold'
    intro a b c d
    simp [coefficient_tmul]
  rw [hz, add_zero]

/-- A block mass and a retained core alone do not prevent total cancellation. -/
theorem duplicate_cancellation (M : V ≃ₗ[k] V) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V) :
    coefficient (M.prodCongr M) g (J.prod J) (sumDual K (-K)) = 0 := by
  apply TensorProduct.ext_fourfold'
  intro a b c d
  simp [coefficient_tmul, sumDual_apply]

end
end Math.MediatorInheritance
