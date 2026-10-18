import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic

/-! Paired-field elimination with a general invertible mass operator.
The second mediator and current live in the algebraic dual. -/
set_option autoImplicit false
namespace Math.MediatorExchange
noncomputable section
open scoped TensorProduct

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def scalarMass (m : k) (hm : m ≠ 0) : V ≃ₗ[k] V := LinearEquiv.smulOfNeZero k V m hm

theorem scalarMass_apply (m : k) (hm : m ≠ 0) (x : V) : scalarMass m hm x = m • x := rfl

theorem scalarMass_symm_apply (m : k) (hm : m ≠ 0) (x : V) :
    (scalarMass m hm).symm x = m⁻¹ • x := rfl

def action (M : V ≃ₗ[k] V) (g : k) (J : V) (K : Module.Dual k V)
    (x : V) (y : Module.Dual k V) : k := y (M x) + g * (y J + K x)

def leftSolution (M : V ≃ₗ[k] V) (g : k) (J : V) : V := -g • M.symm J

def rightSolution (M : V ≃ₗ[k] V) (g : k) (K : Module.Dual k V) : Module.Dual k V :=
  -g • K.comp M.symm.toLinearMap

theorem shifted_action (M : V ≃ₗ[k] V) (g : k) (J : V) (K : Module.Dual k V)
    (x : V) (y : Module.Dual k V) :
    action M g J K (x + leftSolution M g J) (y + rightSolution M g K) =
      y (M x) - g ^ 2 * K (M.symm J) := by
  simp [action, leftSolution, rightSolution, map_add, map_smul, smul_eq_mul]
  ring

theorem on_shell (M : V ≃ₗ[k] V) (g : k) (J : V) (K : Module.Dual k V) :
    action M g J K (leftSolution M g J) (rightSolution M g K) =
      -(g ^ 2) * K (M.symm J) := by
  simpa using shifted_action M g J K 0 0

theorem left_equation (M : V ≃ₗ[k] V) (g : k) (J : V) :
    M (leftSolution M g J) + g • J = 0 := by
  simp [leftSolution]

theorem right_equation (M : V ≃ₗ[k] V) (g : k) (K : Module.Dual k V) :
    (rightSolution M g K).comp M.toLinearMap + g • K = 0 := by
  ext x
  simp [rightSolution]

variable {A B C D : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]

def coefficient (M : V ≃ₗ[k] V) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V) :
    (A ⊗[k] B) ⊗[k] (C ⊗[k] D) →ₗ[k] k :=
  -(g ^ 2) • ((contractRight k V).comp
    (TensorProduct.map (M.symm.toLinearMap.comp J) K)).comp
      (TensorProduct.tensorTensorTensorComm k A B C D).toLinearMap

theorem coefficient_tmul (M : V ≃ₗ[k] V) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (a : A) (b : B) (c : C) (d : D) :
    coefficient M g J K ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d)) =
      -(g ^ 2) * K (b ⊗ₜ[k] d) (M.symm (J (a ⊗ₜ[k] c))) := rfl

theorem coefficient_eq_action (M : V ≃ₗ[k] V) (g : k)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V)
    (a : A) (b : B) (c : C) (d : D) :
    coefficient M g J K ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d)) =
      action M g (J (a ⊗ₜ[k] c)) (K (b ⊗ₜ[k] d))
        (leftSolution M g (J (a ⊗ₜ[k] c)))
        (rightSolution M g (K (b ⊗ₜ[k] d))) := by
  rw [on_shell, coefficient_tmul]

theorem coefficient_eq_zero_iff (M : V ≃ₗ[k] V) (g : k) (hg : g ≠ 0)
    (J : A ⊗[k] C →ₗ[k] V) (K : B ⊗[k] D →ₗ[k] Module.Dual k V) :
    coefficient M g J K = 0 ↔
      ∀ a b c d, K (b ⊗ₜ[k] d) (M.symm (J (a ⊗ₜ[k] c))) = 0 := by
  constructor
  · intro h a b c d
    have hz := DFunLike.congr_fun h ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))
    rw [coefficient_tmul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (pow_ne_zero _ hg))
  · intro h
    apply TensorProduct.ext_fourfold'
    intro a b c d
    simp [coefficient_tmul, h]

variable {W : Type*} [AddCommGroup W] [Module k W]

theorem on_shell_transport (M : V ≃ₗ[k] V) (T : V ≃ₗ[k] W)
    (g : k) (J : V) (K : Module.Dual k V) :
    let N := T.symm.trans (M.trans T)
    let L := K.comp T.symm.toLinearMap
    action N g (T J) L (leftSolution N g (T J)) (rightSolution N g L) =
      action M g J K (leftSolution M g J) (rightSolution M g K) := by
  dsimp only
  rw [on_shell, on_shell]
  simp

/-- Invertible mass and two nonzero sources do not imply nonzero exchange. -/
theorem cancellation_control :
    ∃ (J : Fin 2 → ℚ) (K : Module.Dual ℚ (Fin 2 → ℚ)),
      J ≠ 0 ∧ K ≠ 0 ∧
      action (LinearEquiv.refl ℚ _) 1 J K
        (leftSolution (LinearEquiv.refl ℚ _) 1 J)
        (rightSolution (LinearEquiv.refl ℚ _) 1 K) = 0 := by
  let J : Fin 2 → ℚ := ![1, 1]
  let K : Module.Dual ℚ (Fin 2 → ℚ) :=
    (LinearMap.proj (0 : Fin 2) : Module.Dual ℚ (Fin 2 → ℚ)) -
      (LinearMap.proj (1 : Fin 2) : Module.Dual ℚ (Fin 2 → ℚ))
  refine ⟨J, K, ?_, ?_, ?_⟩
  · intro h
    have hx := congrFun h 0
    norm_num [J] at hx
  · intro h
    have hx := DFunLike.congr_fun h ![1, 0]
    norm_num [K] at hx
  · rw [on_shell]
    norm_num [J, K]

end
end Math.MediatorExchange
