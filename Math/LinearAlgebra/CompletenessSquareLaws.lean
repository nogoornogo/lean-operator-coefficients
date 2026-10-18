import Mathlib.Algebra.Module.Equiv.Basic

/-! Identity and composition laws follow from independently established
completeness squares. This module never defines an output transport. -/
namespace Math.CompletenessSquareLaws
set_option autoImplicit false
variable {k A B C X Y Z : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]

theorem identity (E : A ≃ₗ[k] X) (s : X →ₗ[k] X)
    (h : ∀ a, E a = s (E a)) : ∀ x, s x = x := by
  intro x
  obtain ⟨a,rfl⟩ := E.surjective x
  exact (h a).symm

theorem composition (EA : A ≃ₗ[k] X) (EB : B ≃ₗ[k] Y) (EC : C ≃ₗ[k] Z)
    (p : A →ₗ[k] B) (q : B →ₗ[k] C) (r : A →ₗ[k] C)
    (s : X →ₗ[k] Y) (t : Y →ₗ[k] Z) (u : X →ₗ[k] Z)
    (hp : ∀ a, EB (p a) = s (EA a)) (hq : ∀ b, EC (q b) = t (EB b))
    (hr : ∀ a, EC (r a) = u (EA a)) (hc : ∀ a, q (p a) = r a) :
    ∀ x, t (s x) = u x := by
  intro x
  obtain ⟨a,rfl⟩ := EA.surjective x
  rw [← hp, ← hq, hc, hr]
end Math.CompletenessSquareLaws
