import Math.LinearAlgebra.Selection.MediatorExchange

/-! Simultaneous change of mediator carrier. The dual current transforms
contragrediently; the external source spaces remain fixed. -/
set_option autoImplicit false
namespace Math.MediatorTransport
noncomputable section
open scoped TensorProduct
variable {k V W : Type*} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def mass (T : V ≃ₗ[k] W) (M : V ≃ₗ[k] V) : W ≃ₗ[k] W :=
  T.symm.trans (M.trans T)

variable {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
def source (T : V ≃ₗ[k] W) (J : X →ₗ[k] V) : X →ₗ[k] W := T.toLinearMap.comp J
def observer (T : V ≃ₗ[k] W) (K : Y →ₗ[k] Module.Dual k V) : Y →ₗ[k] Module.Dual k W :=
  T.symm.toLinearMap.dualMap.comp K

theorem mass_apply (T : V ≃ₗ[k] W) (M : V ≃ₗ[k] V) (x : V) :
    mass T M (T x) = T (M x) := by simp [mass]
theorem inverse_apply (T : V ≃ₗ[k] W) (M : V ≃ₗ[k] V) (x : V) :
    (mass T M).symm (T x) = T (M.symm x) := by simp [mass]
theorem observer_apply (T : V ≃ₗ[k] W) (K : Y →ₗ[k] Module.Dual k V) (y : Y) (x : V) :
    observer T K y (T x) = K y x := by simp [observer]

theorem action_eq (T : V ≃ₗ[k] W) (M : V ≃ₗ[k] V) (g : k)
    (J : V) (K : Module.Dual k V) (x : V) (y : Module.Dual k V) :
    MediatorExchange.action (mass T M) g (T J) (K.comp T.symm.toLinearMap)
      (T x) (y.comp T.symm.toLinearMap) = MediatorExchange.action M g J K x y := by
  simp [MediatorExchange.action, mass]

variable {A B C D : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]

theorem coefficient_eq (T : V ≃ₗ[k] W) (M : V ≃ₗ[k] V) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V) :
    MediatorExchange.coefficient (mass T M) g (source T J) (observer T K) =
      MediatorExchange.coefficient M g J K := by
  apply TensorProduct.ext_fourfold'
  intro a b c d
  simp [MediatorExchange.coefficient_tmul, mass, source, observer]

theorem mass_refl (M : V ≃ₗ[k] V) : mass (LinearEquiv.refl k V) M = M := by ext x; rfl
theorem source_refl (J : X →ₗ[k] V) : source (LinearEquiv.refl k V) J = J := by ext x; rfl
theorem observer_refl (K : Y →ₗ[k] Module.Dual k V) :
    observer (LinearEquiv.refl k V) K = K := by ext y x; rfl

variable {Z : Type*} [AddCommGroup Z] [Module k Z]
theorem mass_trans (T : V ≃ₗ[k] W) (S : W ≃ₗ[k] Z) (M : V ≃ₗ[k] V) :
    mass S (mass T M) = mass (T.trans S) M := by ext x; rfl
theorem source_trans (T : V ≃ₗ[k] W) (S : W ≃ₗ[k] Z) (J : X →ₗ[k] V) :
    source S (source T J) = source (T.trans S) J := by ext x; rfl
theorem observer_trans (T : V ≃ₗ[k] W) (S : W ≃ₗ[k] Z) (K : Y →ₗ[k] Module.Dual k V) :
    observer S (observer T K) = observer (T.trans S) K := by ext y x; rfl

/-- Changing the source but not the dual changes the exchange even in one dimension. -/
theorem untransported_dual_control :
    MediatorExchange.action (LinearEquiv.refl ℚ ℚ) 1 1 (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
      (MediatorExchange.leftSolution (LinearEquiv.refl ℚ ℚ) 1 1)
      (MediatorExchange.rightSolution (LinearEquiv.refl ℚ ℚ) 1 LinearMap.id) = -1 ∧
    MediatorExchange.action (LinearEquiv.refl ℚ ℚ) 1 2 (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
      (MediatorExchange.leftSolution (LinearEquiv.refl ℚ ℚ) 1 2)
      (MediatorExchange.rightSolution (LinearEquiv.refl ℚ ℚ) 1 LinearMap.id) = -2 := by
  simp [MediatorExchange.on_shell]

def shear : (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ) where
  toFun x := (x.1 + x.2, x.2)
  invFun x := (x.1 - x.2, x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ext <;> simp; ring
  map_smul' c x := by ext <;> simp [mul_add]

/-- A coordinate change can make a diagonal mass non-diagonal without changing the action. -/
theorem nondiagonal_mass_control :
    mass shear ((LinearEquiv.refl ℚ ℚ).prodCongr
      (MediatorExchange.scalarMass (2 : ℚ) (by norm_num))) (0,1) = (1,2) := by
  norm_num [mass, shear, MediatorExchange.scalarMass]

end
end Math.MediatorTransport
