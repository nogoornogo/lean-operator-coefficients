import Math.LinearAlgebra.Selection.MediatorTransport
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueMediatorInheritance

open Math

/-! Mediator-coordinate transport preserves the actual generated qque sector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Physics.QqueMediatorTransport
noncomputable section
open Representation MediatorTransport
open scoped TensorProduct
variable {H Q U E V W : Type*} [Group H]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (q : Representation ℂ H Q) (u : Representation ℂ H U) (e : Representation ℂ H E)
  (T : V ≃ₗ[ℂ] W) (M : V ≃ₗ[ℂ] V) (g : ℂ)
  (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V)

theorem invariant (h : MediatorQque.IsInvariant q u e M g J K) :
    MediatorQque.IsInvariant q u e (mass T M) g (source T J) (observer T K) :=
  QqueMediatorInheritance.invariant q u e M (mass T M) g J K (source T J) (observer T K)
    (coefficient_eq T M g J K) h

def generated (h : MediatorQque.IsInvariant q u e M g J K) :=
  MediatorQque.sector q u e (mass T M) g (source T J) (observer T K)
    (invariant q u e T M g J K h)

theorem generated_eq (h : MediatorQque.IsInvariant q u e M g J K) :
    generated q u e T M g J K h = MediatorQque.sector q u e M g J K h :=
  QqueMediatorInheritance.sector_eq q u e M (mass T M) g J K (source T J) (observer T K)
    (coefficient_eq T M g J K) h (invariant q u e T M g J K h)

theorem generated_ne_zero_iff (h : MediatorQque.IsInvariant q u e M g J K) :
    generated q u e T M g J K h ≠ 0 ↔ MediatorQque.sector q u e M g J K h ≠ 0 := by
  rw [generated_eq]

end
end Physics.QqueMediatorTransport
