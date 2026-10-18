import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.LinearAlgebra.CoefficientSelectorComposition

/-! Families of prescribed flavor selectors on the existing physical dipole domain. -/
namespace GUT.ComposableDipoleSelection
set_option autoImplicit false
noncomputable section
open Representation Math.CoefficientSelectorComposition
variable {H A B I : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [FiniteDimensional ℂ B]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (mu : I → A) (electron : I → Module.Dual ℂ B)

def residual : (IntertwiningMap a b × IntertwiningMap a b) →ₗ[ℂ] (I → ℂ × ℂ) :=
  combine (fun i => DipoleFlavorSelection.residualSelector a b (mu i) (electron i))
def selector : DipoleFlavorSelection.Coefficients a b →ₗ[ℂ] (I → ℂ × ℂ) :=
  combine (fun i => DipoleFlavorSelection.selector a b (mu i) (electron i))

theorem extraction (c : DipoleFlavorSelection.Coefficients a b) :
    selector a b mu electron c = residual a b mu electron (DipoleSMCoefficient.equiv a b c) := rfl

theorem forbidden_iff : selector a b mu electron = 0 ↔
    ∀ i, DipoleFlavorSelection.residualSelector a b (mu i) (electron i) = 0 := by
  have hs : selector a b mu electron =
      (residual a b mu electron).comp (DipoleSMCoefficient.equiv a b).toLinearMap := rfl
  rw [hs, transport_zero_iff]
  exact combine_zero_iff _

/-- Each prescribed pair may be detected by a different group element. -/
theorem forbidden_of_weights
    (detect : ∀ i, ∃ g : H, ∃ alpha beta : ℂ,
      a g (mu i) = alpha • mu i ∧
      (∀ y, electron i (b g y) = beta * electron i y) ∧ alpha ≠ beta) :
    selector a b mu electron = 0 := by
  change combine _ = 0
  rw [combine_zero_iff]
  intro i
  obtain ⟨g,alpha,beta,hmu,he,hne⟩ := detect i
  exact LinearMap.ext
    (DipoleFlavorSelection.forbidden_of_distinct_weights a b (mu i) (electron i)
      g alpha beta hmu he hne)
end
end GUT.ComposableDipoleSelection
