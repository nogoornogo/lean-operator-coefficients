import Physics.StandardModel.Operators.MediatorQque

open Math

/-! Evaluation of the generated exterior coefficient without unfolding
model-dependent representations or radical carriers. -/
set_option autoImplicit false
namespace GUT.MediatorQqueEvaluation
noncomputable section
open Representation SMEpsilonTensor
open scoped TensorProduct
variable {H Q U E V : Type*} [Group H]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]
  (q : Representation ℂ H Q) (u : Representation ℂ H U) (e : Representation ℂ H E)
  (M : V ≃ₗ[ℂ] V) (g : ℂ)
  (J : Q ⊗[ℂ] U →ₗ[ℂ] V) (K : Q ⊗[ℂ] E →ₗ[ℂ] Module.Dual ℂ V)
  (h : MediatorQque.IsInvariant q u e M g J K)

theorem sector_slots (x y : Q) (a : U) (b : E) (s t z l : WeylSpinor.Space) :
    (MediatorQque.sector q u e M g J K h).val
      (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
        (x ⊗ₜ[ℂ] s) (y ⊗ₜ[ℂ] t) (a ⊗ₜ[ℂ] z) (b ⊗ₜ[ℂ] l))) =
    MediatorExchange.coefficient M g J K ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) *
      (eps2 s t * eps2 z l) -
    MediatorExchange.coefficient M g J K ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) *
      (eps2 t s * eps2 z l) := by
  exact FourSlotAlternation.coefficient_slots _ _ _ _ _ _ _ _

theorem sector_ne_zero_of_slots (x y : Q) (a : U) (b : E) (s t z l : WeylSpinor.Space)
    (hn : MediatorExchange.coefficient M g J K ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) *
      (eps2 s t * eps2 z l) -
      MediatorExchange.coefficient M g J K ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) *
      (eps2 t s * eps2 z l) ≠ 0) : MediatorQque.sector q u e M g J K h ≠ 0 := by
  intro hz
  have he := sector_slots q u e M g J K h x y a b s t z l
  rw [hz] at he
  exact hn he.symm

theorem sector_ne_zero_of_restriction
    {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (iQ : A →ₗ[ℂ] Q) (iU : B →ₗ[ℂ] U) (iE : C →ₗ[ℂ] E)
    (c : (A ⊗[ℂ] A) ⊗[ℂ] (B ⊗[ℂ] C) →ₗ[ℂ] ℂ)
    (hc : ∀ x y a b, MediatorExchange.coefficient M g J K
      ((iQ x ⊗ₜ[ℂ] iQ y) ⊗ₜ[ℂ] (iU a ⊗ₜ[ℂ] iE b)) =
        c ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)))
    (x y : A) (a : B) (b : C) (s t z l : WeylSpinor.Space)
    (hn : c ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) * (eps2 s t * eps2 z l) -
      c ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] b)) * (eps2 t s * eps2 z l) ≠ 0) :
    MediatorQque.sector q u e M g J K h ≠ 0 := by
  apply sector_ne_zero_of_slots q u e M g J K h (iQ x) (iQ y) (iU a) (iE b) s t z l
  simpa only [hc] using hn

end
end GUT.MediatorQqueEvaluation
