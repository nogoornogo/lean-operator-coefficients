import Math.LinearAlgebra.Selection.MediatorInheritance
import Physics.StandardModel.Operators.BaryonOne.Qque.MediatorQque

open Math

/-! Transport of generated invariant and exterior coefficients along an
exchange identity. Structural identities are supplied by MediatorInheritance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Physics.QqueMediatorInheritance
noncomputable section
open Representation
open scoped TensorProduct

variable {H Q U E V W : Type*} [Group H]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (q : Representation ℂ H Q) (u : Representation ℂ H U) (e : Representation ℂ H E)
  (M : V ≃ₗ[ℂ] V) (N : W ≃ₗ[ℂ] W) (g : ℂ)
  (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V)
  (L : Q ⊗[ℂ] U →ₗ[ℂ] W) (R : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ W)

theorem invariant (heq : MediatorExchange.coefficient N g L R =
    MediatorExchange.coefficient M g J K) (h : MediatorQque.IsInvariant q u e M g J K) :
    MediatorQque.IsInvariant q u e N g L R := by
  intro a z
  rw [heq]
  exact h a z

theorem internal_eq (heq : MediatorExchange.coefficient N g L R =
    MediatorExchange.coefficient M g J K)
    (h : MediatorQque.IsInvariant q u e M g J K)
    (h' : MediatorQque.IsInvariant q u e N g L R) :
    MediatorQque.internal q u e N g L R h' = MediatorQque.internal q u e M g J K h := by
  apply DFunLike.ext
  intro z
  exact DFunLike.congr_fun heq z

theorem sector_eq (heq : MediatorExchange.coefficient N g L R =
    MediatorExchange.coefficient M g J K)
    (h : MediatorQque.IsInvariant q u e M g J K)
    (h' : MediatorQque.IsInvariant q u e N g L R) :
    MediatorQque.sector q u e N g L R h' = MediatorQque.sector q u e M g J K h := by
  apply Subtype.ext
  change QqueSpinorExterior.exterior _ _ _ _ = QqueSpinorExterior.exterior _ _ _ _
  rw [internal_eq q u e M N g J K L R heq h h']

end
end Physics.QqueMediatorInheritance
